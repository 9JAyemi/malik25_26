// SVA for mux_4to1. Bind this to the DUT.
module mux_4to1_asserts (
  input logic in0, in1, in2, in3,
  input logic sel0, sel1,
  input logic out
);
  // Functional checks with X-awareness
  always_comb begin
    if (!$isunknown({sel1,sel0})) begin
      unique case ({sel1,sel0})
        2'b00: if (!$isunknown(in0)) assert (out == in0) else $error("mux: out!=in0 when sel=00");
        2'b01: if (!$isunknown(in1)) assert (out == in1) else $error("mux: out!=in1 when sel=01");
        2'b10: if (!$isunknown(in2)) assert (out == in2) else $error("mux: out!=in2 when sel=10");
        2'b11: if (!$isunknown(in3)) assert (out == in3) else $error("mux: out!=in3 when sel=11");
      endcase
    end
  end

  // X propagation when selected input is X
  always_comb begin
    if (!$isunknown({sel1,sel0})) begin
      unique case ({sel1,sel0})
        2'b00: if ($isunknown(in0)) assert ($isunknown(out)) else $error("mux: X not propagated from in0");
        2'b01: if ($isunknown(in1)) assert ($isunknown(out)) else $error("mux: X not propagated from in1");
        2'b10: if ($isunknown(in2)) assert ($isunknown(out)) else $error("mux: X not propagated from in2");
        2'b11: if ($isunknown(in3)) assert ($isunknown(out)) else $error("mux: X not propagated from in3");
      endcase
    end
  end

  // Out follows the selected input on its edges (##0 to avoid race)
  property p_follow_in0; @(posedge in0 or negedge in0) (!sel1 && !sel0) |-> ##0 (out === in0); endproperty
  property p_follow_in1; @(posedge in1 or negedge in1) ( sel0 && !sel1) |-> ##0 (out === in1); endproperty
  property p_follow_in2; @(posedge in2 or negedge in2) (!sel0 &&  sel1) |-> ##0 (out === in2); endproperty
  property p_follow_in3; @(posedge in3 or negedge in3) ( sel0 &&  sel1) |-> ##0 (out === in3); endproperty
  assert property (p_follow_in0);
  assert property (p_follow_in1);
  assert property (p_follow_in2);
  assert property (p_follow_in3);

  // Unselected inputs must not affect out
  property p_unselected_no_effect_i0; @(posedge in0 or negedge in0) ( sel1 ||  sel0) |-> ##0 $stable(out); endproperty
  property p_unselected_no_effect_i1; @(posedge in1 or negedge in1) (!sel0 ||  sel1) |-> ##0 $stable(out); endproperty
  property p_unselected_no_effect_i2; @(posedge in2 or negedge in2) ( sel0 || !sel1) |-> ##0 $stable(out); endproperty
  property p_unselected_no_effect_i3; @(posedge in3 or negedge in3) (!sel0 || !sel1) |-> ##0 $stable(out); endproperty
  assert property (p_unselected_no_effect_i0);
  assert property (p_unselected_no_effect_i1);
  assert property (p_unselected_no_effect_i2);
  assert property (p_unselected_no_effect_i3);

  // Coverage: hit all select combos and observe follow behavior
  always_comb begin
    unique case ({sel1,sel0})
      2'b00: cover (1);
      2'b01: cover (1);
      2'b10: cover (1);
      2'b11: cover (1);
    endcase
  end
  cover property (p_follow_in0);
  cover property (p_follow_in1);
  cover property (p_follow_in2);
  cover property (p_follow_in3);
endmodule

bind mux_4to1 mux_4to1_asserts i_mux_4to1_asserts (.*);