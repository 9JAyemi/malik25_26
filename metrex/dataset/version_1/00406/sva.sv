// SVA for division_module
// Focus: FSM legality, data movement, functional correctness, handshake, and output/valid behavior

module division_module_sva
  #(parameter W = 8)
  (
    input  logic                clk,
    input  logic                rst_n,
    input  logic [W-1:0]        A,
    input  logic [W-1:0]        B,
    input  logic                ready,
    input  logic [W-1:0]        quotient,
    input  logic [W-1:0]        remainder,
    input  logic                valid,

    // Internal taps via bind
    input  logic [W-1:0]        dividend_reg,
    input  logic [W-1:0]        divisor_reg,
    input  logic [W-1:0]        quotient_reg,
    input  logic [W-1:0]        remainder_reg,
    input  logic [2:0]          state
  );

  localparam S0 = 3'b000;
  localparam S1 = 3'b001;
  localparam S2 = 3'b010;
  localparam S3 = 3'b011;

  // Check reset values on clock while reset is active
  a_reset_values: assert property (@(posedge clk)
    !rst_n |-> (state==S0 && dividend_reg==0 && divisor_reg==0 &&
                quotient_reg==0 && remainder_reg==0 && valid==1'b0));

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Known checks (no X/Z after reset released)
  a_knowns: assert property (!$isunknown({state,dividend_reg,divisor_reg,quotient_reg,remainder_reg,quotient,remainder,valid})));

  // FSM legal states only
  a_state_legal: assert property (state inside {S0,S1,S2,S3});

  // State transitions
  a_s0_to_s1:       assert property (state==S0 |=> state==S1);
  a_s1_divnz_to_s2: assert property ((state==S1 && divisor_reg!=0) |=> state==S2);
  a_s1_div0_to_s0:  assert property ((state==S1 && divisor_reg==0) |=> state==S0);
  a_s2_stall:       assert property ((state==S2 && !ready) |=> state==S2);
  a_s2_ready_to_s3: assert property ((state==S2 && ready) |=> state==S3);
  a_s3_to_s0:       assert property (state==S3 |=> state==S0);

  // Capture behavior: S0 latches A/B into dividend_reg/divisor_reg next cycle
  a_capture_inputs: assert property (state==S0 |=> (dividend_reg==$past(A) && divisor_reg==$past(B)));
  a_hold_inputs:    assert property ((state!=S0) |-> ($stable(dividend_reg) && $stable(divisor_reg)));

  // Compute behavior in S1 for non-zero divisor
  a_compute_regs: assert property (
    (state==S1 && divisor_reg!=0)
      |=> (quotient_reg == $past(dividend_reg)/$past(divisor_reg) &&
           remainder_reg == $past(dividend_reg)%$past(divisor_reg)));

  // Division identities post-compute (in S2 and S3)
  a_div_identity_regs: assert property (
    (state inside {S2,S3} && divisor_reg!=0)
      |-> (dividend_reg == divisor_reg*quotient_reg + remainder_reg &&
           remainder_reg <  divisor_reg));

  // Divide-by-zero path: regs cleared, valid asserted next cycle, outputs must not change except in S3
  a_div0_regs_and_valid: assert property (
    (state==S1 && divisor_reg==0)
      |=> (quotient_reg==0 && remainder_reg==0 && valid==1'b1));
  a_outputs_only_in_s3: assert property (
    (!$stable({quotient,remainder})) |-> (state==S3));

  // Output drive and valid behavior in S3
  a_outputs_match_regs_in_s3: assert property (state==S3 |-> (quotient==quotient_reg && remainder==remainder_reg && valid==1'b1));

  // Valid must be low except in S3 or the div-by-zero return cycle
  a_valid_only_when_allowed: assert property (
    ((state inside {S0,S2}) || (state==S1 && divisor_reg!=0)) |-> (valid==1'b0));

  // Stability while waiting in S2 without ready
  a_stability_in_wait: assert property (
    (state==S2 && !ready) |-> ($stable(quotient_reg) && $stable(remainder_reg) &&
                               $stable(dividend_reg) && $stable(divisor_reg) &&
                               $stable(quotient) && $stable(remainder) &&
                               valid==1'b0));

  // Coverage

  // Normal operation with a stall, then ready and output
  c_normal_flow: cover property (
    state==S0 ##1 (state==S1 && divisor_reg!=0)
    ##1 (state==S2 && !ready) ##[1:5] (state==S2 && ready)
    ##1 (state==S3 && valid));

  // Divide-by-zero path covered
  c_div0_flow: cover property (state==S0 ##1 (state==S1 && divisor_reg==0) ##1 (state==S0 && valid));

  // Back-to-back valid results when ready is high (no stall)
  c_back_to_back: cover property (
    (state==S1 && divisor_reg!=0) ##1 (state==S2 && ready) ##1 (state==S3 && valid)
    ##1 state==S0 ##1
    (state==S1 && divisor_reg!=0) ##1 (state==S2 && ready) ##1 (state==S3 && valid));

endmodule

// Bind SVA into DUT (connect internal signals)
bind division_module division_module_sva
  u_division_module_sva (
    .clk         (clk),
    .rst_n       (rst_n),
    .A           (A),
    .B           (B),
    .ready       (ready),
    .quotient    (quotient),
    .remainder   (remainder),
    .valid       (valid),
    .dividend_reg(dividend_reg),
    .divisor_reg (divisor_reg),
    .quotient_reg(quotient_reg),
    .remainder_reg(remainder_reg),
    .state       (state)
  );