// SVA for sky130_fd_sc_lp__a32oi
// Function: Y = ~((A1 & A2 & A3) | (B1 & B2))

module a32oi_sva (
  input logic Y,
  input logic A1, A2, A3,
  input logic B1, B2,
  input logic nand0_out, nand1_out, and0_out_Y
);

  // Trigger on any primary input edge
  `define A32OI_EV (posedge A1 or negedge A1 or \
                     posedge A2 or negedge A2 or \
                     posedge A3 or negedge A3 or \
                     posedge B1 or negedge B1 or \
                     posedge B2 or negedge B2)

  // Optional: flag X/Z on inputs
  assert property (@(`A32OI_EV) !$isunknown({A1,A2,A3,B1,B2}))
    else $error("a32oi: X/Z on inputs");

  // Functional equivalence (when inputs known)
  assert property (@(`A32OI_EV)
                   (!$isunknown({A1,A2,A3,B1,B2})) |->
                   (Y === ~((A1 & A2 & A3) | (B1 & B2))))
    else $error("a32oi: Y != ~(A1&A2&A3 | B1&B2)");

  // Gate-level internal checks (guarded on known drivers)
  assert property (@(`A32OI_EV)
                   (!$isunknown({A1,A2,A3})) |->
                   (nand0_out === ~(A1 & A2 & A3)))
    else $error("a32oi: nand0_out mismatch");

  assert property (@(`A32OI_EV)
                   (!$isunknown({B1,B2})) |->
                   (nand1_out === ~(B1 & B2)))
    else $error("a32oi: nand1_out mismatch");

  assert property (@(`A32OI_EV)
                   (!$isunknown({nand0_out,nand1_out})) |->
                   (and0_out_Y === (nand0_out & nand1_out)))
    else $error("a32oi: and0_out_Y mismatch");

  assert property (@(`A32OI_EV)
                   (!$isunknown(and0_out_Y)) |->
                   (Y === and0_out_Y))
    else $error("a32oi: buf output mismatch");

  // Output known when inputs known
  assert property (@(`A32OI_EV)
                   (!$isunknown({A1,A2,A3,B1,B2})) |->
                   !$isunknown(Y))
    else $error("a32oi: Y unknown with known inputs");

  // Compact functional coverage
  cover property (@(`A32OI_EV) (~(A1&A2&A3) && ~(B1&B2) && (Y==1)));
  cover property (@(`A32OI_EV) ((A1&A2&A3) && ~(B1&B2) && (Y==0)));
  cover property (@(`A32OI_EV) (~(A1&A2&A3) && (B1&B2) && (Y==0)));
  cover property (@(`A32OI_EV) ((A1&A2&A3) && (B1&B2) && (Y==0)));

  // Y toggles in both directions
  cover property (@(`A32OI_EV) (Y ##1 !Y));
  cover property (@(`A32OI_EV) (!Y ##1 Y));

  `undef A32OI_EV
endmodule

// Bind into the DUT to access internal nets
bind sky130_fd_sc_lp__a32oi a32oi_sva u_a32oi_sva (
  .Y(Y),
  .A1(A1), .A2(A2), .A3(A3),
  .B1(B1), .B2(B2),
  .nand0_out(nand0_out),
  .nand1_out(nand1_out),
  .and0_out_Y(and0_out_Y)
);