// SVA for Mux_3x1_W11
// Bind this file alongside the DUT

module Mux_3x1_W11_sva (
  input [1:0]  ctrl,
  input [10:0] D0,
  input [10:0] D1,
  input [10:0] D2,
  input [10:0] S
);
  default clocking cb @(*); endclocking

  // Functional equivalence (4-state accurate)
  a_func: assert property (S === (ctrl==2'b00 ? D0 :
                                  ctrl==2'b01 ? D1 :
                                  ctrl==2'b10 ? D2 : 11'b0));

  // Default path for all non-00/01/10 encodings (including X/Z)
  a_default: assert property ((ctrl!=2'b00 && ctrl!=2'b01 && ctrl!=2'b10) |-> (S === 11'b0));

  // No X/Z on S when selected input is known
  a_known_d0: assert property ((ctrl==2'b00 && !$isunknown(D0)) |-> (!$isunknown(S) && S==D0));
  a_known_d1: assert property ((ctrl==2'b01 && !$isunknown(D1)) |-> (!$isunknown(S) && S==D1));
  a_known_d2: assert property ((ctrl==2'b10 && !$isunknown(D2)) |-> (!$isunknown(S) && S==D2));

  // Non-interference: unselected inputs must not affect S
  a_nonint_00_d1: assert property ((ctrl==2'b00 && $changed(D1)) |-> $stable(S));
  a_nonint_00_d2: assert property ((ctrl==2'b00 && $changed(D2)) |-> $stable(S));
  a_nonint_01_d0: assert property ((ctrl==2'b01 && $changed(D0)) |-> $stable(S));
  a_nonint_01_d2: assert property ((ctrl==2'b01 && $changed(D2)) |-> $stable(S));
  a_nonint_10_d0: assert property ((ctrl==2'b10 && $changed(D0)) |-> $stable(S));
  a_nonint_10_d1: assert property ((ctrl==2'b10 && $changed(D1)) |-> $stable(S));

  // Coverage: hit all selections and default, and observe data pass-through activity
  c_sel_00: cover property (ctrl==2'b00 && S===D0);
  c_sel_01: cover property (ctrl==2'b01 && S===D1);
  c_sel_10: cover property (ctrl==2'b10 && S===D2);
  c_def:    cover property ((ctrl!=2'b00 && ctrl!=2'b01 && ctrl!=2'b10) && S===11'b0);

  c_pass_d0: cover property (ctrl==2'b00 && $changed(D0) && $changed(S) && S===D0);
  c_pass_d1: cover property (ctrl==2'b01 && $changed(D1) && $changed(S) && S===D1);
  c_pass_d2: cover property (ctrl==2'b10 && $changed(D2) && $changed(S) && S===D2);

endmodule

bind Mux_3x1_W11 Mux_3x1_W11_sva i_Mux_3x1_W11_sva (.ctrl(ctrl), .D0(D0), .D1(D1), .D2(D2), .S(S));