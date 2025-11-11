// SVA checker for vga_stripes
// Focus: functional equivalence, sensitivity completeness, stability, X checks, and concise coverage.

module vga_stripes_sva (
  input  logic        VIDON,
  input  logic [9:0]  HC,
  input  logic [9:0]  VC,
  input  logic [17:0] SW,
  input  logic [7:0]  R,
  input  logic [7:0]  G,
  input  logic [7:0]  B
);

  // Sample on any relevant change; ignore checks when inputs are X/Z
  default clocking cb @(VIDON or HC or VC or SW); endclocking
  default disable iff ($isunknown({VIDON,HC,VC}));

  // Outputs must never be X/Z (when inputs known)
  assert property (1 |-> ##0 !$isunknown({R,G,B}));

  // Functional mapping
  // VIDON=0 => black
  assert property ((!VIDON) |-> ##0 (R==8'h00 && G==8'h00 && B==8'h00));
  // VIDON=1 => R=HC[7:0], G=B=VC[7:0]
  assert property (( VIDON) |-> ##0 (R==HC[7:0] && G==VC[7:0] && B==VC[7:0]));
  // G and B always equal by design intent
  assert property (1 |-> ##0 (G==B));

  // Stability: if functional inputs stay stable, outputs must stay stable
  assert property (($stable({VIDON,HC,VC})) |-> ##0 $stable({R,G,B}));

  // Independence from SW (unused by DUT): SW changes alone must not affect outputs
  assert property (($changed(SW) && $stable({VIDON,HC,VC})) |-> ##0 $stable({R,G,B}));

  // Sensitivity completeness checks
  // If only VC changes while VIDON=1, G/B must update in same timestep
  assert property (($changed(VC) && VIDON && $stable({VIDON,HC})) |-> ##0 (G==VC[7:0] && B==VC[7:0]));
  // If only HC changes while VIDON=1, R must update in same timestep (will FAIL with missing HC in sensitivity list)
  assert property (($changed(HC) && VIDON && $stable({VIDON,VC})) |-> ##0 (R==HC[7:0]));

  // Concise functional coverage
  cover property ($rose(VIDON));
  cover property ($fell(VIDON));
  cover property (VIDON && (|HC[9:8]));  // exercise truncation of HC
  cover property (VIDON && (|VC[9:8]));  // exercise truncation of VC
  cover property (VIDON && (HC[7:0]==8'hFF) && (VC[7:0]==8'h00)); // extreme values
  cover property ($changed(HC) && VIDON && $stable(VC));          // scenario that exposes missing HC sensitivity
  cover property ($changed(SW) && $stable({VIDON,HC,VC}));        // SW independence scenario

endmodule

// Bind into DUT
bind vga_stripes vga_stripes_sva sva (
  .VIDON(VIDON),
  .HC(HC),
  .VC(VC),
  .SW(SW),
  .R(R),
  .G(G),
  .B(B)
);