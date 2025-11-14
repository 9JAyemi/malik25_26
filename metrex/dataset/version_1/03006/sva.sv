// SVA for sky130_fd_sc_hd__a311o
// Function: X = (A1 & A2 & A3) | B1 | C1

module sky130_fd_sc_hd__a311o_sva (
  input logic A1, A2, A3, B1, C1, X
);

  // Functional equivalence on any input change (sample after delta)
  assert property (@(A1 or A2 or A3 or B1 or C1)
                   ##0 (X === ((A1 & A2 & A3) | B1 | C1)));

  // Deterministic dominance of OR inputs
  assert property (@(A1 or A2 or A3 or B1 or C1)
                   (B1 === 1'b1) |-> ##0 (X === 1'b1));
  assert property (@(A1 or A2 or A3 or B1 or C1)
                   (C1 === 1'b1) |-> ##0 (X === 1'b1));

  // When B1=C1=0, output equals 3-input AND
  assert property (@(A1 or A2 or A3 or B1 or C1)
                   (B1 === 1'b0 && C1 === 1'b0) |-> ##0 (X === (A1 & A2 & A3)));

  // If all inputs known, output must be known (no X/Z propagation)
  assert property (@(A1 or A2 or A3 or B1 or C1)
                   (!$isunknown({A1,A2,A3,B1,C1})) |-> ##0 (!$isunknown(X)));

  // Minimal, high-value functional coverage

  // OR-path coverage
  cover property (@(A1 or A2 or A3 or B1 or C1) (B1==1'b1) ##0 (X==1'b1));
  cover property (@(A1 or A2 or A3 or B1 or C1) (C1==1'b1) ##0 (X==1'b1));

  // AND-path coverage with B1=C1=0
  cover property (@(A1 or A2 or A3 or B1 or C1)
                  (B1==1'b0 && C1==1'b0 &&  A1 &&  A2 &&  A3) ##0 (X==1'b1)); // 111 -> 1
  cover property (@(A1 or A2 or A3 or B1 or C1)
                  (B1==1'b0 && C1==1'b0 &&  A1 &&  A2 && !A3) ##0 (X==1'b0)); // 110 -> 0
  cover property (@(A1 or A2 or A3 or B1 or C1)
                  (B1==1'b0 && C1==1'b0 &&  A1 && !A2 && !A3) ##0 (X==1'b0)); // 100 -> 0
  cover property (@(A1 or A2 or A3 or B1 or C1)
                  (B1==1'b0 && C1==1'b0 && !A1 && !A2 && !A3) ##0 (X==1'b0)); // 000 -> 0

endmodule

// Bind into DUT
bind sky130_fd_sc_hd__a311o sky130_fd_sc_hd__a311o_sva a311o_sva_bind (.*);