// SVA for shift_adder and submodules (concise, quality-focused)

module sva_shift_reg_mod (
  input logic       CLK,
  input logic       RST,
  input logic       LD,
  input logic [3:0] D,
  input logic [3:0] OUT
);
  // Reset clears
  assert property (@(posedge CLK) RST |=> (OUT == 4'b0));

  // Load on LD
  assert property (@(posedge CLK) disable iff (RST)
                   LD |=> (OUT == $past(D)));

  // Shift-left with zero insert when not LD
  assert property (@(posedge CLK) disable iff (RST)
                   !LD |=> (OUT == {$past(OUT[2:0]), 1'b0}));

  // After a load, 4 cycles of shifting drains to zero
  assert property (@(posedge CLK) disable iff (RST)
                   LD ##1 (!LD)[*4] |-> (OUT == 4'b0));

  // X check: known inputs => known output
  assert property (@(posedge CLK) disable iff (RST)
                   !$isunknown({LD, D, $past(OUT)}) |-> !$isunknown(OUT));

  // Coverage: load then shift out
  cover property (@(posedge CLK) disable iff (RST)
                  LD ##1 (!LD)[*4] ##1 (OUT == 4'b0));
endmodule


module sva_shift_adder_top (
  input  logic        CLK,
  input  logic        RST,
  input  logic        LD,
  input  logic [3:0]  D,
  input  logic [15:0] A,
  input  logic [15:0] B,
  input  logic [15:0] SUM,
  // internal nets from DUT
  input  logic [3:0]  shift_reg,
  input  logic [15:0] signed_sum
);
  function automatic logic [15:0] abs16 (input logic [15:0] x);
    return x[15] ? (~x + 16'd1) : x;
  endfunction

  // Match DUT's signed_adder behavior including 17->16 truncation
  function automatic logic [15:0] exp_signed_sum (input logic [15:0] a, input logic [15:0] b);
    logic [15:0] aa = abs16(a);
    logic [15:0] bb = abs16(b);
    logic [16:0] tmp;
    if (a[15] == b[15])       tmp = {a[15], aa + bb};
    else if (aa > bb)         tmp = {a[15], aa - bb};
    else                      tmp = {b[15], bb - aa};
    return tmp[15:0];
  endfunction

  // signed_adder output correctness
  assert property (@(posedge CLK)
                   !$isunknown({A,B}) |-> (signed_sum == exp_signed_sum(A,B)));

  // Top-level SUM = signed_sum + zero-extended shift_reg (truncated to 16b)
  assert property (@(posedge CLK) disable iff (RST)
                   !$isunknown({A,B,shift_reg}) |->
                   (SUM == (signed_sum + {12'd0, shift_reg})[15:0]));

  // Outputs known when inputs known
  assert property (@(posedge CLK) disable iff (RST)
                   !$isunknown({A,B,shift_reg}) |-> !$isunknown({signed_sum, SUM}));

  // Coverage: signed_adder operation modes
  cover property (@(posedge CLK) (A[15] == B[15])); // same sign (add magnitudes)
  cover property (@(posedge CLK) (A[15] != B[15]) && (abs16(A) >  abs16(B))); // diff signs, |A|>|B|
  cover property (@(posedge CLK) (A[15] != B[15]) && (abs16(A) <  abs16(B))); // diff signs, |A|<|B|
  cover property (@(posedge CLK) (A[15] != B[15]) && (abs16(A) == abs16(B)) && (signed_sum == 16'h0000)); // equal mags -> zero (sign truncated)

  // Coverage: top-level addition overflow (carry-out dropped)
  cover property (@(posedge CLK)
                  ((exp_signed_sum(A,B) + {12'd0, shift_reg}) > 16'hFFFF));
endmodule


// Bind SVA to DUT
bind shift_reg_mod  sva_shift_reg_mod    u_sva_shift_reg_mod  (.CLK(CLK), .RST(RST), .LD(LD), .D(D), .OUT(OUT));
bind shift_adder    sva_shift_adder_top  u_sva_shift_adder_top (.CLK(CLK), .RST(RST), .LD(LD), .D(D), .A(A), .B(B), .SUM(SUM),
                                                               .shift_reg(shift_reg), .signed_sum(signed_sum));