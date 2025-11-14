// SVA for diode_controller
module diode_controller_sva (
  input logic DIODE,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB,
  input logic D1,
  input logic D2,
  input logic D3,
  input logic D4
);

  // Functional mapping when input is known
  property p_map_known;
    @(DIODE or D1 or D2 or D3 or D4)
      !$isunknown(DIODE) |-> (D1===DIODE && D2===DIODE && D3===~DIODE && D4===~DIODE);
  endproperty
  assert property (p_map_known);

  // Unknown propagation when input is unknown
  property p_xprop;
    @(DIODE or D1 or D2 or D3 or D4)
      $isunknown(DIODE) |-> $isunknown({D1,D2,D3,D4});
  endproperty
  assert property (p_xprop);

  // Only two valid output patterns when known
  property p_only_valid_patterns;
    @({D1,D2,D3,D4})
      !$isunknown({D1,D2,D3,D4}) |-> ({D1,D2,D3,D4} inside {4'b1100,4'b0011});
  endproperty
  assert property (p_only_valid_patterns);

  // Structural invariants
  assert property (@(D1 or D2 or D3 or D4)
                   (!$isunknown({D1,D2,D3,D4})) |-> (D1===D2 && D3===D4 && D1===~D3));

  // No spurious output changes without input change
  assert property (@(D1 or D2 or D3 or D4) $changed({D1,D2,D3,D4}) |-> $changed(DIODE));

  // Power/ground/bulk sanity
  assert property (@(VPWR) !$isunknown(VPWR) && VPWR===1'b1);
  assert property (@(VGND) !$isunknown(VGND) && VGND===1'b0);
  assert property (@(VPB or VPWR) VPB===VPWR);
  assert property (@(VNB or VGND) VNB===VGND);

  // Coverage: both polarities and X behavior
  cover property (@(posedge DIODE) (D1 && D2 && !D3 && !D4));
  cover property (@(negedge DIODE) (!D1 && !D2 && D3 && D4));
  cover property (@(DIODE) $isunknown(DIODE) && $isunknown({D1,D2,D3,D4}));

endmodule

bind diode_controller diode_controller_sva sva (
  .DIODE(DIODE), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
  .D1(D1), .D2(D2), .D3(D3), .D4(D4)
);