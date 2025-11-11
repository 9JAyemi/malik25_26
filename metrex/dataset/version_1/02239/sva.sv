// SVA for sky130_fd_sc_hdll__bufinv
// Bind this file after compiling the DUT

module sky130_fd_sc_hdll__bufinv_sva (
  input logic A,
  input logic Y,
  input logic VPWR, VGND, VPB, VNB,
  input logic not0_out_Y
);

  // Power and well ties
  assert property (@(A or Y)
    (VPWR === 1'b1) && (VGND === 1'b0) && (VPB === VPWR) && (VNB === VGND));

  // No Zs on internal/output
  assert property (@(Y)           !(Y === 1'bz));
  assert property (@(not0_out_Y)  !(not0_out_Y === 1'bz));

  // Functional: binary A => Y == ~A (inverter behavior through buffer)
  assert property (@(A or Y) !$isunknown(A) |-> ##0 (Y === ~A));

  // Stage-wise correctness
  assert property (@(A or not0_out_Y) !$isunknown(A) |-> ##0 (not0_out_Y === ~A));
  assert property (@(not0_out_Y or Y) !$isunknown(not0_out_Y) |-> ##0 (Y === not0_out_Y));

  // X propagation: unknown A must yield unknown Y and internal
  assert property (@(A or Y)          $isunknown(A) |-> ##0 $isunknown(Y));
  assert property (@(A or not0_out_Y) $isunknown(A) |-> ##0 $isunknown(not0_out_Y));

  // Causality: A toggle causes Y toggle; Y only toggles if A toggles
  assert property (@(A or Y) ($rose(A) || $fell(A)) |-> ##0 ($rose(Y) || $fell(Y)));
  assert property (@(A or Y) ($rose(Y) || $fell(Y)) |-> ##0 ($rose(A) || $fell(A)));

  // Coverage
  cover property (@(A) $rose(A));
  cover property (@(A) $fell(A));
  cover property (@(Y) $rose(Y));
  cover property (@(Y) $fell(Y));
  cover property (@(A) $isunknown(A));
  cover property (@(Y) $isunknown(Y));

endmodule

bind sky130_fd_sc_hdll__bufinv sky130_fd_sc_hdll__bufinv_sva
  u_sva ( .A(A), .Y(Y), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB), .not0_out_Y(not0_out_Y) );