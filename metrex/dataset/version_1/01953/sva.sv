// SVA for full_adder and four_bit_adder
// Provide clk and rst_n from your environment and bind to DUTs.

// 1) full_adder assertions + coverage
module full_adder_sva (
  input logic clk, rst_n,
  input logic A, B, Cin,
  input logic S, Cout
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Knownness
  ap_known: assert property (!$isunknown({A,B,Cin})) |-> !$isunknown({S,Cout});

  // Functional equivalence (arithmetic)
  ap_add:   assert property (!$isunknown({A,B,Cin})) |-> {Cout,S} == ({1'b0,A} + {1'b0,B} + Cin);

  // Logic-form checks
  ap_sum:   assert property (!$isunknown({A,B,Cin})) |-> S    == (A ^ B ^ Cin);
  ap_cout:  assert property (!$isunknown({A,B,Cin})) |-> Cout == ((A & B) | (Cin & (A ^ B)));

  // Full truth-table coverage (8 combos)
  cover property (!$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b000);
  cover property (!$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b001);
  cover property (!$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b010);
  cover property (!$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b011);
  cover property (!$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b100);
  cover property (!$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b101);
  cover property (!$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b110);
  cover property (!$isunknown({A,B,Cin}) && {A,B,Cin} == 3'b111);

  // Carry/no-carry occurrence
  cover property (!$isunknown({A,B,Cin}) && Cout);
  cover property (!$isunknown({A,B,Cin}) && !Cout);
endmodule


// 2) four_bit_adder assertions + coverage
// Includes internal connectivity checks via S_int, C0..C2
module four_bit_adder_sva (
  input logic clk, rst_n,
  input logic [3:0] A, B,
  input logic       Cin,
  input logic [3:0] S,
  input logic       Cout,
  input logic [3:0] S_int,
  input logic       C0, C1, C2
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Knownness
  ap_known: assert property (!$isunknown({A,B,Cin})) |-> !$isunknown({S,Cout});

  // End-to-end arithmetic correctness
  ap_add4: assert property (!$isunknown({A,B,Cin})) |-> {Cout,S} == ({1'b0,A} + {1'b0,B} + Cin);

  // S mapping
  ap_s_map: assert property (!$isunknown({A,B,Cin})) |-> S == S_int;

  // Per-bit sum and carry chain
  ap_b0_s:  assert property (!$isunknown({A[0],B[0],Cin})) |-> S_int[0] == (A[0]^B[0]^Cin);
  ap_c0:    assert property (!$isunknown({A[0],B[0],Cin})) |-> C0 == ((A[0]&B[0]) | ((A[0]^B[0]) & Cin));

  ap_b1_s:  assert property (!$isunknown({A[1],B[1],C0})) |-> S_int[1] == (A[1]^B[1]^C0);
  ap_c1:    assert property (!$isunknown({A[1],B[1],C0})) |-> C1 == ((A[1]&B[1]) | ((A[1]^B[1]) & C0));

  ap_b2_s:  assert property (!$isunknown({A[2],B[2],C1})) |-> S_int[2] == (A[2]^B[2]^C1);
  ap_c2:    assert property (!$isunknown({A[2],B[2],C1})) |-> C2 == ((A[2]&B[2]) | ((A[2]^B[2]) & C1));

  ap_b3_s:  assert property (!$isunknown({A[3],B[3],C2})) |-> S_int[3] == (A[3]^B[3]^C2);
  ap_cout:  assert property (!$isunknown({A[3],B[3],C2})) |-> Cout == ((A[3]&B[3]) | ((A[3]^B[3]) & C2));

  // Coverage: all 512 input combinations, carry/no-carry, full ripple propagate, MSB generate
  covergroup cg4 @(posedge clk);
    cp_all_inputs: coverpoint {A,B,Cin} { bins all[] = {[0:511]}; }
    cp_cout:       coverpoint Cout;
  endgroup
  cg4 cg4_i = new();

  cover property (!$isunknown({A,B,Cin}) && ((A^B)==4'hF) && Cin && Cout); // full propagate chain
  cover property (!$isunknown({A,B,Cin}) && (A[3]&B[3]) && Cout);          // MSB generate
endmodule


// Example bind statements (connect clk/rst_n from your env)
// bind full_adder     full_adder_sva     u_full_adder_sva     (.clk(clk), .rst_n(rst_n), .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout));
// bind four_bit_adder four_bit_adder_sva u_four_bit_adder_sva (.clk(clk), .rst_n(rst_n), .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout), .S_int(S_int), .C0(C0), .C1(C1), .C2(C2));