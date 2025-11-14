// SVA for mag_comparator
module mag_comparator_sva #(parameter int n = 4) (
  input  logic [n-1:0] A,
  input  logic [n-1:0] B,
  input  logic         GT,
  input  logic         EQ,
  input  logic         LT
);
  localparam logic [n-1:0] MIN = '0;
  localparam logic [n-1:0] MAX = {n{1'b1}};

  // Ignore checks when inputs contain X/Z
  default disable iff ($isunknown({A,B}));

  // Functional equivalence (sample outputs after delta to avoid races)
  assert property (@(A or B) 1'b1 |-> ##0 ({GT,EQ,LT} == { (A>B), (A==B), (A<B) }));

  // Exactly one output asserted and no X/Z on outputs (when inputs are 2-state)
  assert property (@(A or B) 1'b1 |-> ##0 ($onehot({GT,EQ,LT}) && !$isunknown({GT,EQ,LT})));

  // Functional coverage (key outcomes and boundaries)
  cover property (@(A or B) ##0 (A >  B));
  cover property (@(A or B) ##0 (A == B));
  cover property (@(A or B) ##0 (A <  B));

  cover property (@(A or B) ##0 (A==MIN && B==MIN));
  cover property (@(A or B) ##0 (A==MAX && B==MAX));
  cover property (@(A or B) ##0 (A==MIN && B==MAX));
  cover property (@(A or B) ##0 (A==MAX && B==MIN));
endmodule

// Bind into DUT
bind mag_comparator mag_comparator_sva #(.n(n)) u_mag_comparator_sva (.A(A), .B(B), .GT(GT), .EQ(EQ), .LT(LT));