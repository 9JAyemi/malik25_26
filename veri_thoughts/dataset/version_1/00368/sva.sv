// SVA checker for full_adder
module full_adder_sva (
  input logic clk,
  input logic A, B, Cin,
  input logic Sum, Cout
);
  default clocking cb @(posedge clk); endclocking

  // Outputs must be known when inputs are known
  assert property (!$isunknown({A,B,Cin})) |-> !$isunknown({Sum,Cout});

  // Functional correctness (sampled every clock)
  assert property (!$isunknown({A,B,Cin})) |-> (Sum == (A ^ B ^ Cin));
  assert property (!$isunknown({A,B,Cin})) |-> (Cout == ((A & B) | (Cin & (A ^ B))));

  // Propagate / Generate / Kill semantics
  assert property (!$isunknown({A,B,Cin}) && (A ^ B)) |-> (Cout == Cin) && (Sum == ~Cin);
  assert property (!$isunknown({A,B,Cin}) && (A & B))  |-> (Cout == 1) && (Sum == Cin);
  assert property (!$isunknown({A,B,Cin}) && (!A && !B)) |-> (Cout == 0) && (Sum == Cin);

  // Full truth-table coverage (with expected outputs)
  cover property ({A,B,Cin} == 3'b000 && Sum==0 && Cout==0);
  cover property ({A,B,Cin} == 3'b001 && Sum==1 && Cout==0);
  cover property ({A,B,Cin} == 3'b010 && Sum==1 && Cout==0);
  cover property ({A,B,Cin} == 3'b011 && Sum==0 && Cout==1);
  cover property ({A,B,Cin} == 3'b100 && Sum==1 && Cout==0);
  cover property ({A,B,Cin} == 3'b101 && Sum==0 && Cout==1);
  cover property ({A,B,Cin} == 3'b110 && Sum==0 && Cout==1);
  cover property ({A,B,Cin} == 3'b111 && Sum==1 && Cout==1);

  // Toggle coverage
  cover property ($rose(Sum));
  cover property ($fell(Sum));
  cover property ($rose(Cout));
  cover property ($fell(Cout));
endmodule

// Bind into DUT (connect clk from your TB)
bind full_adder full_adder_sva u_full_adder_sva (
  .clk(tb_clk),
  .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout)
);