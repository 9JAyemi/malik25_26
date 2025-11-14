// SVA for sky130_fd_sc_hs__o21a
// Function per given RTL: X = A1 & A2 & B1 & VPWR & VGND

module sky130_fd_sc_hs__o21a_sva (
  input logic X,
  input logic A1,
  input logic A2,
  input logic B1,
  input logic VPWR,
  input logic VGND
);

  // Functional equivalence (4-state exact match, deferred to avoid delta issues)
  always_comb begin
    assert #0 (X === (A1 & A2 & B1 & VPWR & VGND))
      else $error("o21a func mismatch: X=%b A1=%b A2=%b B1=%b VPWR=%b VGND=%b",
                  X, A1, A2, B1, VPWR, VGND);
  end

  // Sensitization properties: when all other inputs are 1, a single input edge controls X
  property rise_drives_high(i, a, b, c, d);
    @(posedge i) (a && b && c && d) |-> ##0 X;
  endproperty
  property fall_drives_low(i, a, b, c, d);
    @(negedge i) (a && b && c && d) |-> ##0 !X;
  endproperty

  // Assert single-input control behavior for all inputs
  assert property (rise_drives_high(A1,  A2, B1, VPWR, VGND));
  assert property (fall_drives_low (A1,  A2, B1, VPWR, VGND));
  assert property (rise_drives_high(A2,  A1, B1, VPWR, VGND));
  assert property (fall_drives_low (A2,  A1, B1, VPWR, VGND));
  assert property (rise_drives_high(B1,  A1, A2, VPWR, VGND));
  assert property (fall_drives_low (B1,  A1, A2, VPWR, VGND));
  assert property (rise_drives_high(VPWR, A1, A2, B1,  VGND));
  assert property (fall_drives_low (VPWR, A1, A2, B1,  VGND));
  assert property (rise_drives_high(VGND, A1, A2, B1,  VPWR));
  assert property (fall_drives_low (VGND, A1, A2, B1,  VPWR));

  // Simple implications for clarity
  // If X is 1, all inputs must be 1
  assert property (@(posedge X) A1 && A2 && B1 && VPWR && VGND);

  // Coverage
  cover property (@(posedge X) A1 && A2 && B1 && VPWR && VGND); // observe high
  cover property (@(negedge X) 1'b1);                            // observe low

  // Per-input toggle coverage under sensitized condition
  cover property (@(posedge A1)  A2 && B1 && VPWR && VGND ##0 X);
  cover property (@(negedge A1)  A2 && B1 && VPWR && VGND ##0 !X);
  cover property (@(posedge A2)  A1 && B1 && VPWR && VGND ##0 X);
  cover property (@(negedge A2)  A1 && B1 && VPWR && VGND ##0 !X);
  cover property (@(posedge B1)  A1 && A2 && VPWR && VGND ##0 X);
  cover property (@(negedge B1)  A1 && A2 && VPWR && VGND ##0 !X);
  cover property (@(posedge VPWR) A1 && A2 && B1  && VGND ##0 X);
  cover property (@(negedge VPWR) A1 && A2 && B1  && VGND ##0 !X);
  cover property (@(posedge VGND) A1 && A2 && B1  && VPWR ##0 X);
  cover property (@(negedge VGND) A1 && A2 && B1  && VPWR ##0 !X);

endmodule

bind sky130_fd_sc_hs__o21a sky130_fd_sc_hs__o21a_sva sva_inst (.*);