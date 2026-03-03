// SVA for sky130_fd_sc_hd__o211a: X = (A1 | A2) & B1 & C1
// Concise, functionally complete, and 4-state aware. Uses ##0 to allow delta-cycle settle.

module sky130_fd_sc_hd__o211a_sva (
  input logic X,
  input logic A1,
  input logic A2,
  input logic B1,
  input logic C1
);

  // Combinational reference
  logic ref;
  assign ref = (A1 | A2) & B1 & C1;

  // Functional equivalence (4-state exact), sampled on any relevant change, allow 1-delta settle
  assert property (@(A1 or A2 or B1 or C1 or X) ##0 (X === ref))
    else $error("o211a func mismatch: X=%b ref=%b A1=%b A2=%b B1=%b C1=%b", X, ref, A1, A2, B1, C1);

  // Known-output guarantee when all inputs are known
  assert property (@(A1 or A2 or B1 or C1) !$isunknown({A1,A2,B1,C1}) |-> ##0 !$isunknown(X))
    else $error("o211a X is X/Z with known inputs");

  // Output only changes when some input changes (no spontaneous X glitches)
  assert property (@(X or A1 or A2 or B1 or C1) $changed(X) |-> $changed({A1,A2,B1,C1}))
    else $error("o211a X changed without input cause");

  // Strong controlling-zero checks (AND stage)
  assert property (@(B1 or C1 or A1 or A2 or X) (B1 === 1'b0) |-> ##0 (X === 1'b0))
    else $error("o211a B1=0 did not force X=0");
  assert property (@(B1 or C1 or A1 or A2 or X) (C1 === 1'b0) |-> ##0 (X === 1'b0))
    else $error("o211a C1=0 did not force X=0");

  // OR stage exposure when B1=C1=1 (holds even with unknown A1/A2, due to 4-state ===)
  assert property (@(A1 or A2 or B1 or C1 or X) (B1 === 1'b1 && C1 === 1'b1) |-> ##0 (X === (A1 | A2)))
    else $error("o211a B1=C1=1 did not make X==(A1|A2)");

  // Minimal yet meaningful coverage
  // Toggles
  cover property (@(posedge A1));
  cover property (@(negedge A1));
  cover property (@(posedge A2));
  cover property (@(negedge A2));
  cover property (@(posedge B1));
  cover property (@(negedge B1));
  cover property (@(posedge C1));
  cover property (@(negedge C1));
  cover property (@(posedge X));
  cover property (@(negedge X));

  // Key functional minterms
  cover property (@(A1 or A2 or B1 or C1 or X) ##0 (B1===1 && C1===1 && A1===1 && A2===0 && X===1));
  cover property (@(A1 or A2 or B1 or C1 or X) ##0 (B1===1 && C1===1 && A1===0 && A2===1 && X===1));
  cover property (@(A1 or A2 or B1 or C1 or X) ##0 (B1===1 && C1===1 && A1===1 && A2===1 && X===1));
  cover property (@(A1 or A2 or B1 or C1 or X) ##0 (B1===1 && C1===1 && A1===0 && A2===0 && X===0));
  cover property (@(B1 or C1 or X) ##0 (B1===0 && X===0));
  cover property (@(B1 or C1 or X) ##0 (C1===0 && X===0));

endmodule

// Bind into the DUT
bind sky130_fd_sc_hd__o211a sky130_fd_sc_hd__o211a_sva u_o211a_sva (
  .X (X),
  .A1(A1),
  .A2(A2),
  .B1(B1),
  .C1(C1)
);