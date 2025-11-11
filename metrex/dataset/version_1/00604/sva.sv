// SVA for sky130_fd_sc_lp__and3b
// Concise, power-aware, combinational-accurate (uses ##0 to observe NBA updates)

module sky130_fd_sc_lp__and3b_sva (
  input  wire A_N,
  input  wire B,
  input  wire C,
  input  wire VPWR,
  input  wire VGND,
  input  wire VPB,
  input  wire VNB,
  input  wire X
);

  // Combinational sampling event
  event comb_ev;
  always @* -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  // Convenience lets
  let PG = (VPWR === 1'b1) && (VGND === 1'b0) && (VPB === 1'b1) && (VNB === 1'b0);
  let KI = !$isunknown({A_N,B,C});

  // Check well/bias ties (common for sky130 cells)
  assert property (VPB === VPWR);
  assert property (VNB === VGND);

  // Functional equivalence when power good and inputs known
  assert property (disable iff (!PG) KI |-> ##0 (X === (A_N & B & C)));

  // Output must be known when inputs are known (under PG)
  assert property (disable iff (!PG) KI |-> ##0 !$isunknown(X));

  // Safety: any known 0 input forces output low (under PG)
  assert property (disable iff (!PG)
                   ((A_N===1'b0) || (B===1'b0) || (C===1'b0)) |-> ##0 (X===1'b0));

  // Sanity: output high only if all inputs high (under PG)
  assert property (disable iff (!PG) (X===1'b1) |-> (A_N===1'b1 && B===1'b1 && C===1'b1));

  // Purely combinational: if inputs stable, output stable (under PG)
  assert property (disable iff (!PG) $stable({A_N,B,C}) |-> ##0 $stable(X));

  // Minimal but meaningful functional coverage (under PG)
  cover property (PG);                                 // power good seen
  cover property (PG && A_N && B && C ##0 X===1'b1);   // all-high case
  cover property (PG && (A_N==1'b0) && B && C ##0 X==1'b0); // A_N low dominates
  cover property (PG && A_N && (B==1'b0) && C ##0 X==1'b0); // B low dominates
  cover property (PG && A_N && B && (C==1'b0) ##0 X==1'b0); // C low dominates
  cover property (PG && $rose(X));                     // observe 0->1 toggle
  cover property (PG && $fell(X));                     // observe 1->0 toggle

endmodule

// Bind into DUT
bind sky130_fd_sc_lp__and3b sky130_fd_sc_lp__and3b_sva sva_i (.*);