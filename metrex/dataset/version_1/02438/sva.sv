// SVA for mux4to1 (acts as 2:1 due to 1-bit sel)
// Bindable, clockless concurrent assertions and coverage

module mux4to1_sva (
  input logic [7:0] in0,
  input logic [7:0] in1,
  input logic       sel,
  input logic [7:0] out
);
  // Functional correctness: out == selected input
  property p_func; @(*) out == (sel ? in1 : in0); endproperty
  assert property (p_func);

  // Out does not respond to the unselected input toggling
  property p_un1_noeff; @(*) (sel==0 && $stable(sel) && $stable(in0) && $changed(in1)) |-> $stable(out); endproperty
  assert property (p_un1_noeff);
  property p_un0_noeff; @(*) (sel==1 && $stable(sel) && $stable(in1) && $changed(in0)) |-> $stable(out); endproperty
  assert property (p_un0_noeff);

  // Stability when nothing changes
  property p_quiescent; @(*) ($stable(sel) && $stable(in0) && $stable(in1)) |-> $stable(out); endproperty
  assert property (p_quiescent);

  // Known-ness: if selected path is known, out must be known
  property p_no_x_out; @(*) (!$isunknown(sel) && (sel ? !$isunknown(in1) : !$isunknown(in0))) |-> !$isunknown(out); endproperty
  assert property (p_no_x_out);

  // Disallow X/Z on sel (prevents latch due to missing default)
  assert property (@(*) !$isunknown(sel));

  // Coverage: both selections, transitions, and data propagation
  cover property (@(*) sel==0);
  cover property (@(*) sel==1);
  cover property (@(*) $rose(sel));
  cover property (@(*) $fell(sel));
  cover property (@(*) (sel==0 && $changed(in0) && !$isunknown(in0) && out==in0));
  cover property (@(*) (sel==1 && $changed(in1) && !$isunknown(in1) && out==in1));
endmodule

bind mux4to1 mux4to1_sva u_mux4to1_sva(.in0(in0), .in1(in1), .sel(sel), .out(out));