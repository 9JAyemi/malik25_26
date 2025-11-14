// SVA for ripple_carry_adder and full_adder
// Focused, concise, and bound to the DUTs (checks internal carry chain too)

checker rca_checker #(int WIDTH = 4)
(
  input logic [WIDTH-1:0] A, B,
  input logic             Cin,
  input logic [WIDTH-1:0] Sum,
  input logic             Cout,
  input logic [WIDTH:0]   C
);
  default clocking cb @(*); endclocking
  default disable iff ($isunknown({A,B,Cin,Sum,Cout,C}));

  // Basic X checks
  a_no_x_in:  assert property (!$isunknown({A,B,Cin}));
  a_no_x_out: assert property (!$isunknown({Sum,Cout}));

  // Structural ties
  a_c0:        assert property (C[0] == Cin);
  a_cout_tie:  assert property (Cout == C[WIDTH]);

  // Bit-wise full-adder equations for each stage
  genvar i;
  for (i = 0; i < WIDTH; i++) begin
    a_sum_bit:   assert property (Sum[i]   == (A[i] ^ B[i] ^ C[i]));
    a_carry_bit: assert property (C[i+1]  == ((A[i] & B[i]) | (C[i] & (A[i] ^ B[i]))));

    // Lightweight functional coverage: generate/propagate/kill seen at this bit
    cp_gen_i:  cover property (A[i] & B[i]);
    cp_prop_i: cover property (A[i] ^ B[i]);
    cp_kill_i: cover property (~A[i] & ~B[i]);
  end

  // End-to-end arithmetic equivalence
  a_add_equiv: assert property ({Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin));

  // Corner-case coverage
  cp_zero:            cover property ((A == '0) && (B == '0) && (Cin == 1'b0));
  cp_all_ones:        cover property ((&A) && (&B) && (Cin == 1'b1));
  cp_full_propagate:  cover property (Cin && &(A ^ B)); // full-width propagate chain
endchecker

bind ripple_carry_adder rca_checker #(.WIDTH(WIDTH))
  rca_chk (.A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout), .C(C));

checker fa_checker
(
  input logic A, B, Cin,
  input logic Sum, Cout
);
  default clocking cb @(*); endclocking
  default disable iff ($isunknown({A,B,Cin,Sum,Cout}));

  a_no_x_in:  assert property (!$isunknown({A,B,Cin}));
  a_no_x_out: assert property (!$isunknown({Sum,Cout}));

  a_sum:      assert property (Sum  == (A ^ B ^ Cin));
  a_carry:    assert property (Cout == ((A & B) | (Cin & (A ^ B))));
  a_add:      assert property ({Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin));

  // Minimal coverage
  cp_any:     cover property (1'b1); // ensure sampling occurs
endchecker

bind full_adder fa_checker fa_chk (.A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout));