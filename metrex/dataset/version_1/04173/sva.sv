// SVA for mux_2to1. Bind this file; no DUT changes needed.

module mux_2to1_sva(input logic in0, in1, sel, input logic out);

  // Functional equivalence (post-NBA): out must match selected input when inputs are known
  assert property (@(in0 or in1 or sel)
                   !$isunknown({sel,in0,in1}) |-> ##0 (out === (sel ? in1 : in0)))
    else $error("mux_2to1: out != (sel ? in1 : in0)");

  // Selected input drives out on its change
  assert property (@(posedge in0 or negedge in0)
                   sel==1'b0 && !$isunknown(sel) |-> ##0 (out===in0))
    else $error("mux_2to1: out did not follow in0 when sel=0");

  assert property (@(posedge in1 or negedge in1)
                   sel==1'b1 && !$isunknown(sel) |-> ##0 (out===in1))
    else $error("mux_2to1: out did not follow in1 when sel=1");

  // Unselected input must not disturb out
  assert property (@(posedge in1 or negedge in1)
                   sel==1'b0 && !$isunknown(sel) |-> ##0 $stable(out))
    else $error("mux_2to1: out changed due to in1 while sel=0");

  assert property (@(posedge in0 or negedge in0)
                   sel==1'b1 && !$isunknown(sel) |-> ##0 $stable(out))
    else $error("mux_2to1: out changed due to in0 while sel=1");

  // On sel edges, out reflects correct input (with inputs known)
  assert property (@(posedge sel) !$isunknown(in1) |-> ##0 (out===in1))
    else $error("mux_2to1: out incorrect on sel rising to 1");

  assert property (@(negedge sel) !$isunknown(in0) |-> ##0 (out===in0))
    else $error("mux_2to1: out incorrect on sel falling to 0");

  // Out must be known when all inputs are known
  assert property (@(in0 or in1 or sel)
                   !$isunknown({sel,in0,in1}) |-> ##0 !$isunknown(out))
    else $error("mux_2to1: out is X/Z with known inputs");

  // Coverage: both paths exercised and propagation observed
  cover property (@(posedge sel) ##0 (out===in1));
  cover property (@(negedge sel) ##0 (out===in0));
  cover property (@(posedge in0 or negedge in0) sel==1'b0 ##0 (out===in0));
  cover property (@(posedge in1 or negedge in1) sel==1'b1 ##0 (out===in1));
  cover property (@(sel) (in0!==in1) ##0 (out=== (sel ? in1 : in0)));

endmodule

bind mux_2to1 mux_2to1_sva sva_mux_2to1 (.*);