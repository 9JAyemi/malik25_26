// SVA for mux_2to1. Bind into DUT for continuous checking.
module mux_2to1_sva;
  // Structural equivalence of internal nets
  always_comb begin
    assert (not_sel === ~sel) else $error("not_sel != ~sel");
    assert (a_and_sel === (a & not_sel)) else $error("a_and_sel != a & ~sel");
    assert (b_and_not_sel === (b & sel)) else $error("b_and_not_sel != b & sel");
    assert (y === (a_and_sel | b_and_not_sel)) else $error("y != (a_and_sel | b_and_not_sel)");
  end

  // Functional mux behavior and X-propagation sanity
  always_comb begin
    if (!$isunknown(sel)) begin
      assert (y === (sel ? b : a)) else $error("y != selected input");
      assert (!(a_and_sel && b_and_not_sel)) else $error("both product terms high");
    end
    if (!( $isunknown(a) || $isunknown(b) || $isunknown(sel) ))
      assert (!$isunknown(y)) else $error("clean inputs produced X/Z on y");
  end

  // Concurrent functional check on any input change
  assert property (@(a or b or sel) !$isunknown(sel) |-> (y === (sel ? b : a)));

  // Coverage: exercise both paths and values
  cover property (@(a or b or sel) (!$isunknown(sel) && sel==0 && y===a));
  cover property (@(a or b or sel) (!$isunknown(sel) && sel==1 && y===b));
  cover property (@(a or b or sel) (!$isunknown({a,sel}) && sel==0 && a==0 && y==0));
  cover property (@(a or b or sel) (!$isunknown({a,sel}) && sel==0 && a==1 && y==1));
  cover property (@(a or b or sel) (!$isunknown({b,sel}) && sel==1 && b==0 && y==0));
  cover property (@(a or b or sel) (!$isunknown({b,sel}) && sel==1 && b==1 && y==1));
  cover property (@(posedge sel) (!$isunknown(b) && y===b));
  cover property (@(negedge sel) (!$isunknown(a) && y===a));
endmodule

bind mux_2to1 mux_2to1_sva m2to1_sva();