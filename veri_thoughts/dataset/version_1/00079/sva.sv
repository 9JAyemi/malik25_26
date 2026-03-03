// SVA for mux_4to1 (concise, full functional check + key covers/glitch checks)
module mux_4to1_sva (
  input  logic [3:0] in0, in1, in2, in3,
  input  logic [1:0] sel,
  input  logic [3:0] out
);
  default clocking cb @(*); endclocking

  // Golden functional equivalence (matches case semantics incl. default on X/Z sel)
  property p_func_eq;
    out == ((sel===2'b00) ? in0 :
            (sel===2'b01) ? in1 :
            (sel===2'b10) ? in2 :
            (sel===2'b11) ? in3 : 4'b0);
  endproperty
  assert property (p_func_eq);

  // Default path when sel has X/Z
  assert property ( $isunknown(sel) |-> (out==4'b0) );

  // Knownness preservation on selected path
  assert property ( (sel===2'b00 && !$isunknown(in0)) |-> (!$isunknown(out) && out==in0) );
  assert property ( (sel===2'b01 && !$isunknown(in1)) |-> (!$isunknown(out) && out==in1) );
  assert property ( (sel===2'b10 && !$isunknown(in2)) |-> (!$isunknown(out) && out==in2) );
  assert property ( (sel===2'b11 && !$isunknown(in3)) |-> (!$isunknown(out) && out==in3) );

  // No-glitch: unselected inputs must not affect out when sel and selected input are stable
  assert property ( sel===2'b00 && !$changed(sel) && !$changed(in0) &&
                    ($changed(in1)||$changed(in2)||$changed(in3)) |-> !$changed(out) );
  assert property ( sel===2'b01 && !$changed(sel) && !$changed(in1) &&
                    ($changed(in0)||$changed(in2)||$changed(in3)) |-> !$changed(out) );
  assert property ( sel===2'b10 && !$changed(sel) && !$changed(in2) &&
                    ($changed(in0)||$changed(in1)||$changed(in3)) |-> !$changed(out) );
  assert property ( sel===2'b11 && !$changed(sel) && !$changed(in3) &&
                    ($changed(in0)||$changed(in1)||$changed(in2)) |-> !$changed(out) );

  // Coverage: exercise each select and default, and observe selected-path propagation
  cover property ( sel===2'b00 && out==in0 );
  cover property ( sel===2'b01 && out==in1 );
  cover property ( sel===2'b10 && out==in2 );
  cover property ( sel===2'b11 && out==in3 );
  cover property ( $isunknown(sel) && out==4'b0 );

  cover property ( sel===2'b00 && $changed(in0) && $changed(out) );
  cover property ( sel===2'b01 && $changed(in1) && $changed(out) );
  cover property ( sel===2'b10 && $changed(in2) && $changed(out) );
  cover property ( sel===2'b11 && $changed(in3) && $changed(out) );
endmodule

// Bind into DUT
bind mux_4to1 mux_4to1_sva sva_mux_4to1 (.in0(in0),.in1(in1),.in2(in2),.in3(in3),.sel(sel),.out(out));