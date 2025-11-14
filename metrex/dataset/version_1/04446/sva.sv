// SVA for sky130_fd_sc_lp__nor4b
// Function: Y = ~(A | B | C | ~D_N) = (~A & ~B & ~C & D_N)

`ifndef SKY130_FD_SC_LP__NOR4B_SVA
`define SKY130_FD_SC_LP__NOR4B_SVA

module sky130_fd_sc_lp__nor4b_sva (
  input logic A,
  input logic B,
  input logic C,
  input logic D_N,
  input logic Y
);

  // Functional equivalence on any input change (4-state aware)
  assert property (@(A or B or C or D_N)
                   Y === ~(A | B | C | ~D_N));

  // Knownness: if all inputs known, output must be known
  assert property (@(A or B or C or D_N)
                   (!$isunknown({A,B,C,D_N})) |-> (!$isunknown(Y)));

  // Controlling values force Y low regardless of other inputs
  assert property (@(A)   (A   === 1'b1) |-> (Y === 1'b0));
  assert property (@(B)   (B   === 1'b1) |-> (Y === 1'b0));
  assert property (@(C)   (C   === 1'b1) |-> (Y === 1'b0));
  assert property (@(D_N) (D_N === 1'b0) |-> (Y === 1'b0));

  // Only minterm that yields Y=1
  assert property (@(A or B or C or D_N)
                   (A===1'b0 && B===1'b0 && C===1'b0 && D_N===1'b1) |-> (Y===1'b1));

  // No spontaneous output changes (combinational sanity)
  assert property (@(Y) $changed({A,B,C,D_N}));

  // Coverage: key states and transitions
  cover property (@(A or B or C or D_N)
                  (A==1'b0 && B==1'b0 && C==1'b0 && D_N==1'b1 && Y==1'b1)); // Y=1 case
  cover property (@(posedge Y) 1);
  cover property (@(negedge Y) 1);
  cover property (@(posedge A)   Y==1'b0);
  cover property (@(posedge B)   Y==1'b0);
  cover property (@(posedge C)   Y==1'b0);
  cover property (@(negedge D_N) Y==1'b0);

endmodule

bind sky130_fd_sc_lp__nor4b sky130_fd_sc_lp__nor4b_sva sva_nor4b_i (.*);

`endif