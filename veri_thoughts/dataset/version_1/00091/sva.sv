// SVA checker for mux4to1. Bind this to the DUT.
// Focus: correctness, X/Z guarding on selects, and functional coverage.

module mux4to1_sva
(
  input  logic [7:0] out,
  input  logic [7:0] in0,
  input  logic [7:0] in1,
  input  logic [7:0] in2,
  input  logic [7:0] in3,
  input  logic       sel0,
  input  logic       sel1
);

  // Guard: selects must be 0/1 only (no X/Z)
  always @* begin
    assert (!$isunknown({sel1, sel0}))
      else $error("mux4to1: sel has X/Z: sel1=%b sel0=%b", sel1, sel0);
  end

  // Functional equivalence to a 4:1 mux at all times
  always @* begin
    logic [7:0] exp;
    exp = sel1 ? (sel0 ? in3 : in2)
               : (sel0 ? in1 : in0);
    assert (out === exp)
      else $error("mux4to1: mismatch sel=%b%b exp=0x%0h got=0x%0h", sel1, sel0, exp, out);
  end

  // Basic functional coverage: hit all select paths with correct output
  always @* begin
    cover (!$isunknown({sel1, sel0}) && {sel1, sel0}==2'b00 && out === in0);
    cover (!$isunknown({sel1, sel0}) && {sel1, sel0}==2'b01 && out === in1);
    cover (!$isunknown({sel1, sel0}) && {sel1, sel0}==2'b10 && out === in2);
    cover (!$isunknown({sel1, sel0}) && {sel1, sel0}==2'b11 && out === in3);
  end

  // Transition coverage across all select states (on any select edge)
  sequence s00; !$isunknown({sel1,sel0}) && {sel1,sel0}==2'b00; endsequence
  sequence s01; !$isunknown({sel1,sel0}) && {sel1,sel0}==2'b01; endsequence
  sequence s10; !$isunknown({sel1,sel0}) && {sel1,sel0}==2'b10; endsequence
  sequence s11; !$isunknown({sel1,sel0}) && {sel1,sel0}==2'b11; endsequence

  cover property (@(posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1)
                  s00 ##1 s01 ##1 s10 ##1 s11);

endmodule

// Bind into the DUT
bind mux4to1 mux4to1_sva mux4to1_sva_i (
  .out(out), .in0(in0), .in1(in1), .in2(in2), .in3(in3), .sel0(sel0), .sel1(sel1)
);