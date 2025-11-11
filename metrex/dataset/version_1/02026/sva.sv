// SVA for bitwise_operators
// Bind example:
//   bind bitwise_operators bitwise_operators_sva #(.n(n)) sva_i (.*);

module bitwise_operators_sva #(parameter int n = 4)
(
  input logic [n-1:0] A,
  input logic [n-1:0] B,
  input logic [n-1:0] C1,
  input logic [n-1:0] C2,
  input logic [n-1:0] C3,
  input logic [n-1:0] C4
);
  localparam logic [n-1:0] ONES = {n{1'b1}};

  // Fundamental correctness (combinational, 4-state safe when inputs known)
  assert property (@(A or B) disable iff ($isunknown({A,B})) C1 === (A & B));
  assert property (@(A or B) disable iff ($isunknown({A,B})) C2 === (A | B));
  assert property (@(A or B) disable iff ($isunknown({A,B})) C3 === (A ^ B));
  assert property (@(A or B) disable iff ($isunknown({A,B})) C4 === (~A));

  // Outputs must be known when inputs are known
  assert property (@(A or B) disable iff ($isunknown({A,B})) !$isunknown({C1,C2,C3,C4}));

  // Cross-output consistency identities
  assert property (@(A or B) disable iff ($isunknown({A,B})) (C1 | C3) === C2);      // (A&B)|(A^B) == (A|B)
  assert property (@(A or B) disable iff ($isunknown({A,B})) (C1 & C3) === '0);      // disjoint parts of OR

  // Dependency/independence checks for NOT path
  assert property (@(A or B) disable iff ($isunknown({A,B})) $changed(B) && $stable(A) |-> $stable(C4)); // C4 independent of B
  assert property (@(A or B) disable iff ($isunknown({A,B})) $changed(A) && $stable(B) |-> $changed(C4)); // C4 follows A

  // Functional coverage (key corner cases)
  cover property (@(A or B) !$isunknown({A,B}) && (A == '0)  && (B == '0));
  cover property (@(A or B) !$isunknown({A,B}) && (A == ONES) && (B == ONES));
  cover property (@(A or B) !$isunknown({A,B}) && (A == B));
  cover property (@(A or B) !$isunknown({A,B}) && (A == ~B));
  cover property (@(A or B) !$isunknown({A,B}) && $onehot(A) && $onehot(B) && (A != B));
endmodule