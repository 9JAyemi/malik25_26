// SVA for mux4_to_1_async_reset design
// Bind these checkers to the DUT to verify combinational correctness, X-prop, and basic coverage.

module mux2to1_sva(input [3:0] in0, in1, input sel, input [3:0] out);
  // Functional correctness
  assert property (@(*) out == (sel ? in1 : in0))
    else $error("mux2to1: out != (sel ? in1 : in0)");

  // X-propagation: if inputs/select known, out must be known
  assert property (@(*) !$isunknown({in0,in1,sel}) |-> !$isunknown(out))
    else $error("mux2to1: out unknown with known inputs/select");

  // Coverage: both select values exercised
  cover property (@(*) sel==0 && out==in0);
  cover property (@(*) sel==1 && out==in1);
endmodule

module mux4to1_sva(input [3:0] in0,in1,in2,in3, input sel, input [3:0] out);
  // NOTE: Given RTL, this "4to1" effectively selects only in0 or in3
  assert property (@(*) out == (sel ? in3 : in0))
    else $error("mux4to1: out != (sel ? in3 : in0)");

  assert property (@(*) !$isunknown({in0,in1,in2,in3,sel}) |-> !$isunknown(out))
    else $error("mux4to1: out unknown with known inputs/select");

  cover property (@(*) sel==0 && out==in0);
  cover property (@(*) sel==1 && out==in3);
endmodule

module mux4_to_1_async_reset_sva(
  input [3:0] in0,in1,in2,in3,
  input [1:0] sel,
  input reset,
  input [3:0] out
);
  // Tap internal nets via hierarchical names when bound inside DUT scope
  // If your tool requires explicit ports for these, expose them; otherwise hierarchical refs below are used.
  // Stage-level checks (hierarchical references assume bind inside mux4_to_1_async_reset)
  // mux1_out == (sel[1] ? in3 : in0)
  assert property (@(*) $root.mux4_to_1_async_reset.mux1_out == (sel[1] ? in3 : in0))
    else $error("Top: mux1_out mismatch");
  // mux2_out == (sel[0] ? in3 : in0)
  assert property (@(*) $root.mux4_to_1_async_reset.mux2_out == (sel[0] ? in3 : in0))
    else $error("Top: mux2_out mismatch");
  // mux3_out == (sel[1] ? mux2_out : mux1_out)
  assert property (@(*) $root.mux4_to_1_async_reset.mux3_out ==
                          (sel[1] ? $root.mux4_to_1_async_reset.mux2_out
                                  : $root.mux4_to_1_async_reset.mux1_out))
    else $error("Top: mux3_out mismatch");
  // mux4_out == (reset ? 0 : mux3_out)
  assert property (@(*) $root.mux4_to_1_async_reset.mux4_out ==
                          (reset ? 4'b0 : $root.mux4_to_1_async_reset.mux3_out))
    else $error("Top: mux4_out mismatch");

  // End-to-end functionality
  assert property (@(*) out == (reset ? 4'b0 : ((sel==2'b11) ? in3 : in0)))
    else $error("Top: out functional mismatch");

  // Out must be known when inputs/select/reset are known
  assert property (@(*) !$isunknown({in0,in1,in2,in3,sel,reset}) |-> !$isunknown(out))
    else $error("Top: out unknown with known inputs/select/reset");

  // Coverage: exercise reset and all select combinations
  cover property (@(*) reset==1 && out==4'b0);
  cover property (@(*) reset==0 && sel==2'b11 && out==in3);
  cover property (@(*) reset==0 && sel!=2'b11 && out==in0);
  cover property (@(*) sel==2'b00);
  cover property (@(*) sel==2'b01);
  cover property (@(*) sel==2'b10);
  cover property (@(*) sel==2'b11);
endmodule

// Bind checkers
bind mux2to1                mux2to1_sva              u_mux2to1_sva(.*);
bind mux4to1                mux4to1_sva              u_mux4to1_sva(.*);
bind mux4_to_1_async_reset  mux4_to_1_async_reset_sva u_top_sva(.*);