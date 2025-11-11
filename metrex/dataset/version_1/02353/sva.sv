// SVA for comparator_2bit
module comparator_2bit_sva (
  input logic        clk,       // free-running sample clock
  input logic        rst_n,     // tie high if not used
  input logic [1:0]  A,
  input logic [1:0]  B,
  input logic [1:0]  C
);
  default clocking cb @(posedge clk); endclocking

  // Expected combinational behavior (purely from A/B)
  logic exp_c1, exp_c0;
  always_comb begin
    exp_c1 = (A[1] > B[1]);
    exp_c0 = (A[1] == B[1]) ? (A[0] >= B[0]) : (A[1] < B[1]);
  end

  // Core functional correctness
  assert property (disable iff (!rst_n) C[1] == exp_c1);
  assert property (disable iff (!rst_n) C[0] == exp_c0);

  // Structural/encoding sanity
  assert property (disable iff (!rst_n) C != 2'b11);
  assert property (disable iff (!rst_n) (A[1] != B[1]) |-> (C[0] == ~C[1]));
  assert property (disable iff (!rst_n) (A[1] == B[1]) |-> (C[1] == 1'b0));
  assert property (disable iff (!rst_n) (A == B) |-> (C == 2'b01));
  assert property (disable iff (!rst_n) !$isunknown(C));

  // Functional coverage (key categories)
  cover property (disable iff (!rst_n) (A[1] >  B[1]) && (C == 2'b10));
  cover property (disable iff (!rst_n) (A[1] <  B[1]) && (C == 2'b01));
  cover property (disable iff (!rst_n) (A[1] == B[1]) && (A[0] >= B[0]) && (C == 2'b01));
  cover property (disable iff (!rst_n) (A[1] == B[1]) && (A[0] <  B[0]) && (C == 2'b00));

  // Exhaustive input combination coverage (A,B = 0..3)
  cover property (disable iff (!rst_n) (A==2'd0 && B==2'd0));
  cover property (disable iff (!rst_n) (A==2'd0 && B==2'd1));
  cover property (disable iff (!rst_n) (A==2'd0 && B==2'd2));
  cover property (disable iff (!rst_n) (A==2'd0 && B==2'd3));
  cover property (disable iff (!rst_n) (A==2'd1 && B==2'd0));
  cover property (disable iff (!rst_n) (A==2'd1 && B==2'd1));
  cover property (disable iff (!rst_n) (A==2'd1 && B==2'd2));
  cover property (disable iff (!rst_n) (A==2'd1 && B==2'd3));
  cover property (disable iff (!rst_n) (A==2'd2 && B==2'd0));
  cover property (disable iff (!rst_n) (A==2'd2 && B==2'd1));
  cover property (disable iff (!rst_n) (A==2'd2 && B==2'd2));
  cover property (disable iff (!rst_n) (A==2'd2 && B==2'd3));
  cover property (disable iff (!rst_n) (A==2'd3 && B==2'd0));
  cover property (disable iff (!rst_n) (A==2'd3 && B==2'd1));
  cover property (disable iff (!rst_n) (A==2'd3 && B==2'd2));
  cover property (disable iff (!rst_n) (A==2'd3 && B==2'd3));

  // Output encoding coverage
  cover property (disable iff (!rst_n) C==2'b00);
  cover property (disable iff (!rst_n) C==2'b01);
  cover property (disable iff (!rst_n) C==2'b10);
endmodule

// Example bind (tie rst_n=1'b1 if no reset is available)
// bind comparator_2bit comparator_2bit_sva u_comparator_2bit_sva (.clk(clk), .rst_n(1'b1), .A(A), .B(B), .C(C));