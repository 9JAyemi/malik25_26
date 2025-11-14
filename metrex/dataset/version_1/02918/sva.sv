// SVA for or4 and the sky130 cell; bind without modifying DUT

// Checker for the wrapper or4: X = A | B | C | ~D and internal bus composition
module or4_sva (
  input logic A, B, C, D,
  input logic X,
  input logic [3:0] or_inputs
);
  // Functional correctness (when inputs are known)
  property p_or4_func;
    @(A or B or C or D or X)
      (!$isunknown({A,B,C,D})) |-> (X === (A | B | C | ~D));
  endproperty
  assert property (p_or4_func);

  // Internal wiring/packing is correct
  assert property (@(A or B or C or D or or_inputs) (or_inputs === {A, B, C, ~D}));

  // Minimal but meaningful functional coverage
  // Only-false case
  cover property (@(A or B or C or D or X) (!A && !B && !C &&  D && !X));
  // Each single driver can raise X
  cover property (@(posedge A) (!B && !C &&  D) |-> X);
  cover property (@(posedge B) (!A && !C &&  D) |-> X);
  cover property (@(posedge C) (!A && !B &&  D) |-> X);
  cover property (@(negedge D) (!A && !B && !C) |-> X);
  // Only way X can fall
  cover property (@(posedge D) (!A && !B && !C) |-> !X);
endmodule

bind or4 or4_sva u_or4_sva(.A(A), .B(B), .C(C), .D(D), .X(X), .or_inputs(or_inputs));


// Checker for the sky130_fd_sc_ms__or4b_1 cell model: pure 4-input OR of its pins
module sky130_fd_sc_ms__or4b_1_sva (
  input logic A, B, C, D,
  input logic X
);
  // Cell functional correctness (when inputs are known)
  assert property (@(A or B or C or D or X)
                   (!$isunknown({A,B,C,D})) |-> (X === (A | B | C | D)));

  // Light coverage on the cell truth space
  cover property (@(A or B or C or D or X) (!A && !B && !C && !D && !X));
  cover property (@(posedge A) (!B && !C && !D) |-> X);
endmodule

bind sky130_fd_sc_ms__or4b_1 sky130_fd_sc_ms__or4b_1_sva u_cell_sva(.A(A), .B(B), .C(C), .D(D), .X(X));