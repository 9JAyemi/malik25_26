// SVA checkers for full_adder and four_bit_adder
// Provide a free-running clock at $root.clk (or edit bind to your clock)

// Checker for 1-bit full adder
module full_adder_sva (
  input logic clk,
  input logic A, B, Cin,
  input logic S, Cout
);
  // Functional correctness (single concise equivalence)
  property p_fa_sum_ok;
    @(posedge clk) $changed({A,B,Cin}) |-> ##0 {Cout,S} == (A + B + Cin);
  endproperty
  assert property (p_fa_sum_ok);

  // Truth-table coverage (all 8 input combinations)
  cover property (@(posedge clk) {A,B,Cin} == 3'b000);
  cover property (@(posedge clk) {A,B,Cin} == 3'b001);
  cover property (@(posedge clk) {A,B,Cin} == 3'b010);
  cover property (@(posedge clk) {A,B,Cin} == 3'b011);
  cover property (@(posedge clk) {A,B,Cin} == 3'b100);
  cover property (@(posedge clk) {A,B,Cin} == 3'b101);
  cover property (@(posedge clk) {A,B,Cin} == 3'b110);
  cover property (@(posedge clk) {A,B,Cin} == 3'b111);

  // Basic toggle coverage on outputs
  cover property (@(posedge clk) $rose(Cout));
  cover property (@(posedge clk) $fell(Cout));
  cover property (@(posedge clk) $rose(S));
  cover property (@(posedge clk) $fell(S));
endmodule

bind full_adder full_adder_sva u_full_adder_sva (
  .clk($root.clk),
  .A(A), .B(B), .Cin(Cin),
  .S(S), .Cout(Cout)
);

// Checker for 4-bit ripple-carry adder
module four_bit_adder_sva (
  input logic clk,
  input logic [3:0] A, B,
  input logic       Cin,
  input logic [3:0] S,
  input logic       Cout,
  // internal carries
  input logic c1, c2, c3
);
  // End-to-end correctness
  property p_sum4_ok;
    @(posedge clk) $changed({A,B,Cin}) |-> ##0 {Cout,S} == (A + B + Cin);
  endproperty
  assert property (p_sum4_ok);

  // Stage-by-stage carry/sum correctness (hooks and ripple)
  property p_b0; @(posedge clk) $changed({A[0],B[0],Cin}) |-> ##0 {c1,   S[0]} == (A[0] + B[0] + Cin); endproperty
  property p_b1; @(posedge clk) $changed({A[1],B[1],c1 }) |-> ##0 {c2,   S[1]} == (A[1] + B[1] + c1 ); endproperty
  property p_b2; @(posedge clk) $changed({A[2],B[2],c2 }) |-> ##0 {c3,   S[2]} == (A[2] + B[2] + c2 ); endproperty
  property p_b3; @(posedge clk) $changed({A[3],B[3],c3 }) |-> ##0 {Cout, S[3]} == (A[3] + B[3] + c3 ); endproperty
  assert property (p_b0);
  assert property (p_b1);
  assert property (p_b2);
  assert property (p_b3);

  // Concise but meaningful coverage
  // Extremes
  cover property (@(posedge clk) {Cout,S} == 5'b0_0000);
  cover property (@(posedge clk) {Cout,S} == 5'b1_1111);
  // Full propagate chain (carry ripples through all bits)
  cover property (@(posedge clk) ((A^B) == 4'hF) && Cin && Cout);
  // Generate and kill at LSB
  cover property (@(posedge clk)  A[0] &&  B[0] && c1);
  cover property (@(posedge clk) !A[0] && !B[0] && Cin && !c1);
  // Internal carry activity
  cover property (@(posedge clk) $rose(c1));
  cover property (@(posedge clk) $rose(c2));
  cover property (@(posedge clk) $rose(c3));
  cover property (@(posedge clk) $rose(Cout));
endmodule

bind four_bit_adder four_bit_adder_sva u_four_bit_adder_sva (
  .clk($root.clk),
  .A(A), .B(B), .Cin(Cin),
  .S(S), .Cout(Cout),
  .c1(c1), .c2(c2), .c3(c3)
)