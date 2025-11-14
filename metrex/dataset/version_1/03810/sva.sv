// SVA for mux_2to1
module mux_2to1_sva (input logic sel, in0, in1, out);

  // Functional equivalence (4-state accurate)
  always_comb begin
    assert #0 (out === (sel ? in1 : in0))
      else $error("mux_2to1: out != (sel?in1:in0)");
    // If selected path is known, out must be known
    if (!$isunknown(sel) && !$isunknown(sel ? in1 : in0))
      assert #0 (!$isunknown(out))
        else $error("mux_2to1: out X while selected path known");
  end

  // Non-selected input must not affect output (no glitch)
  property p_mask_in1_no_glitch;
    @(posedge in1 or negedge in1) (sel===1'b0 && $stable(in0)) |-> ##0 $stable(out);
  endproperty
  assert property (p_mask_in1_no_glitch);

  property p_mask_in0_no_glitch;
    @(posedge in0 or negedge in0) (sel===1'b1 && $stable(in1)) |-> ##0 $stable(out);
  endproperty
  assert property (p_mask_in0_no_glitch);

  // Coverage: both data paths exercised and sel-switch behavior
  cover property (@(posedge in0 or negedge in0) sel===1'b0 ##0 out===in0);
  cover property (@(posedge in1 or negedge in1) sel===1'b1 ##0 out===in1);
  cover property (@(posedge sel or negedge sel) (in0!==in1) ##0 $changed(out));
  cover property (@(posedge sel or negedge sel) (in0===in1) ##0 $stable(out));

endmodule

bind mux_2to1 mux_2to1_sva mux_2to1_sva_i (.*);