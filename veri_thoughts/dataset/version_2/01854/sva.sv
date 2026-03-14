module FSM_sva #(
  parameter int n = 4,
  parameter int m = 2,
  parameter int s = 8,
  parameter int c = 3
)(
  input  logic              clk,
  input  logic [n-1:0]      in,
  input  logic [m-1:0]      out,
  // Internal DUT signals (bind these to RTL regs)
  input  logic [c-1:0]      current_state,
  input  logic [c-1:0]      next_state
);
  // Analysis: clock=clk; no reset present. Mixed logic: sequential state reg + combinational next_state/out. FSM with 8 encoded states; next_state depends on one in[] bit per state; out is Moore mapping of current_state.

  // Mirror RTL state encodings (width matches RTL style)
  localparam [c-1:0] S0 = 3'b000,
                     S1 = 3'b001,
                     S2 = 3'b011,
                     S3 = 3'b010,
                     S4 = 3'b110,
                     S5 = 3'b111,
                     S6 = 3'b101,
                     S7 = 3'b100;

  ///// State register update /////
  // State register captures prior next_state each cycle (after first cycle).
  check_state_reg_updates_from_next: assert property (
    @(posedge clk) $past(1'b1) |-> (current_state == $past(next_state))
  );

  ///// Next-state combinational rules /////
  // Next-state rule in S0 (uses in[0]).
  if (n >= 1) begin : g_in0_rules
    check_next_state_rule_s0: assert property (
      @(posedge clk) (current_state == S0) |-> (next_state == (in[0] ? S1 : S0))
    );
    // Next-state rule in S4 (uses in[0]).
    check_next_state_rule_s4: assert property (
      @(posedge clk) (current_state == S4) |-> (next_state == (in[0] ? S5 : S3))
    );
  end

  // Next-state rule in S1 (uses in[1]).
  if (n >= 2) begin : g_in1_rules
    check_next_state_rule_s1: assert property (
      @(posedge clk) (current_state == S1) |-> (next_state == (in[1] ? S2 : S0))
    );
    // Next-state rule in S5 (uses in[1]).
    check_next_state_rule_s5: assert property (
      @(posedge clk) (current_state == S5) |-> (next_state == (in[1] ? S6 : S4))
    );
  end

  // Next-state rule in S2 (uses in[2]).
  if (n >= 3) begin : g_in2_rules
    check_next_state_rule_s2: assert property (
      @(posedge clk) (current_state == S2) |-> (next_state == (in[2] ? S3 : S1))
    );
    // Next-state rule in S6 (uses in[2]).
    check_next_state_rule_s6: assert property (
      @(posedge clk) (current_state == S6) |-> (next_state == (in[2] ? S7 : S5))
    );
  end

  // Next-state rule in S3 (uses in[3]).
  if (n >= 4) begin : g_in3_rules
    check_next_state_rule_s3: assert property (
      @(posedge clk) (current_state == S3) |-> (next_state == (in[3] ? S4 : S2))
    );
    // Next-state rule in S7 (uses in[3]).
    check_next_state_rule_s7: assert property (
      @(posedge clk) (current_state == S7) |-> (next_state == (in[3] ? S0 : S6))
    );
  end

  ///// Output mapping (Moore) /////
  // Output for S0 is 2'b00.
  check_output_rule_s0: assert property (
    @(posedge clk) (current_state == S0) |-> (out == 2'b00)
  );
  // Output for S1 is 2'b01.
  check_output_rule_s1: assert property (
    @(posedge clk) (current_state == S1) |-> (out == 2'b01)
  );
  // Output for S2 is 2'b10.
  check_output_rule_s2: assert property (
    @(posedge clk) (current_state == S2) |-> (out == 2'b10)
  );
  // Output for S3 is 2'b11.
  check_output_rule_s3: assert property (
    @(posedge clk) (current_state == S3) |-> (out == 2'b11)
  );
  // Output for S4 is 2'b00.
  check_output_rule_s4: assert property (
    @(posedge clk) (current_state == S4) |-> (out == 2'b00)
  );
  // Output for S5 is 2'b01.
  check_output_rule_s5: assert property (
    @(posedge clk) (current_state == S5) |-> (out == 2'b01)
  );
  // Output for S6 is 2'b10.
  check_output_rule_s6: assert property (
    @(posedge clk) (current_state == S6) |-> (out == 2'b10)
  );
  // Output for S7 is 2'b11.
  check_output_rule_s7: assert property (
    @(posedge clk) (current_state == S7) |-> (out == 2'b11)
  );

endmodule