// SVA for sky130_fd_sc_hd__a311oi: Y = ~((A1 & A2 & A3) | B1 | C1)
module sky130_fd_sc_hd__a311oi_sva;

  // Sample on any change to DUT pins (including power)
  default clocking cb @(A1 or A2 or A3 or B1 or C1 or Y or VPWR or VGND or VPB or VNB); endclocking

  // Functional equivalence (4-state)
  assert property (##0 (Y === ~((A1 & A2 & A3) | B1 | C1)));

  // Deterministic 0 conditions
  assert property ((B1===1'b1 || C1===1'b1) |-> ##0 (Y===1'b0));
  assert property ((A1===1'b1 && A2===1'b1 && A3===1'b1) |-> ##0 (Y===1'b0));

  // Deterministic 1 condition
  assert property ((A1===1'b0 && A2===1'b0 && A3===1'b0 && B1===1'b0 && C1===1'b0) |-> ##0 (Y===1'b1));

  // When all inputs are known, Y must be known and correct (2-state check)
  assert property (!$isunknown({A1,A2,A3,B1,C1}) |-> ##0 (! $isunknown(Y) && (Y == ~((A1 & A2 & A3) | B1 | C1))));

  // If Y is X, then some input must be X and no OR-term is forcing 1
  assert property ((Y===1'bx) |-> ($isunknown({A1,A2,A3,B1,C1}) && (B1!==1'b1) && (C1!==1'b1)));

  // Power pins constant
  assert property (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);

  // Coverage
  cover property (##0 (Y===1'b0));
  cover property (##0 (Y===1'b1));
  cover property ((B1===1'b1) ##0 (Y===1'b0));
  cover property ((C1===1'b1) ##0 (Y===1'b0));
  cover property ((A1===1'b1 && A2===1'b1 && A3===1'b1 && B1===1'b0 && C1===1'b0) ##0 (Y===1'b0));
  cover property ((A1===1'b0 && A2===1'b0 && A3===1'b0 && B1===1'b0 && C1===1'b0) ##0 (Y===1'b1));
  cover property ((B1===1'b0 && C1===1'b0 && (A1===1'b0 || A2===1'b0 || A3===1'b0)) ##0 (Y===1'b1));
  cover property ((B1===1'b0 && C1===1'b0 && $isunknown({A1,A2,A3}) && !(A1===1'b0 || A2===1'b0 || A3===1'b0)) ##0 (Y===1'bx));

endmodule

bind sky130_fd_sc_hd__a311oi sky130_fd_sc_hd__a311oi_sva sva_a311oi();