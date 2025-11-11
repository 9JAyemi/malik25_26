// SVA for sky130_fd_sc_ms__a21o: X = (A1 & A2) | B1

module sky130_fd_sc_ms__a21o_sva (
  input logic A1, A2, B1, X
);

  default clocking cb @(A1 or A2 or B1 or X); endclocking

  // Functional equivalence with 4-state awareness; allow delta-cycle settle
  assert property (1'b1 |-> ##0 (X === ((A1 & A2) | B1)));

  // No X/Z on inputs; and if inputs known, output must be known
  assert property (!$isunknown({A1,A2,B1}));
  assert property (!$isunknown({A1,A2,B1}) |-> ##0 !$isunknown(X));

  // OR dominance by B1; AND path selected when B1 is 0 and inputs known
  assert property ((B1 === 1'b1) |-> ##0 (X === 1'b1));
  assert property ((B1 === 1'b0 && !$isunknown({A1,A2})) |-> ##0 (X === (A1 & A2)));

  // Output only changes when B1 or (A1&A2) changes
  assert property ($changed(X) |-> ($changed(B1) or $changed(A1 & A2)));

  // If inputs stable, output must remain stable
  assert property ($stable({A1,A2,B1}) |-> ##0 $stable(X));

  // Functional coverage of all input combinations with expected X
  cover property (({A1,A2,B1} === 3'b000) && (X === 1'b0));
  cover property (({A1,A2,B1} === 3'b001) && (X === 1'b1));
  cover property (({A1,A2,B1} === 3'b010) && (X === 1'b0));
  cover property (({A1,A2,B1} === 3'b011) && (X === 1'b1));
  cover property (({A1,A2,B1} === 3'b100) && (X === 1'b0));
  cover property (({A1,A2,B1} === 3'b101) && (X === 1'b1));
  cover property (({A1,A2,B1} === 3'b110) && (X === 1'b1));
  cover property (({A1,A2,B1} === 3'b111) && (X === 1'b1));

endmodule

bind sky130_fd_sc_ms__a21o sky130_fd_sc_ms__a21o_sva i_a21o_sva (.A1(A1), .A2(A2), .B1(B1), .X(X));