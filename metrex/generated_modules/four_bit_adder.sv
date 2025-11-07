// SVA checker for four_bit_adder
// Bind this module to the DUT and drive clk/rst_n from TB.

module four_bit_adder_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic        Cin,
  input  logic [3:0]  S,
  input  logic        Cout
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Golden 5-bit sum (includes carry-out bit)
  let sum5 = ({1'b0,A} + {1'b0,B} + Cin);

  // Functional correctness: packed {Cout,S} equals golden sum
  property p_add_correct;
    !$isunknown({A,B,Cin}) |-> (!$isunknown({S,Cout}) && {Cout,S} == sum5);
  endproperty
  assert property (p_add_correct)
    else $error("four_bit_adder mismatch: A=%0h B=%0h Cin=%0b got {C,S}=%0h exp=%0h",
                A, B, Cin, {Cout,S}, sum5);

  // Sanity: outputs must be 0/1 when inputs are 0/1
  assert property ( !$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout}) )
    else $error("four_bit_adder X/Z on outputs with clean inputs");

  // Key functional covers (exercise edges, carry, extremes)
  cover property (Cin == 0);
  cover property (Cin == 1);
  cover property (Cout == 0);
  cover property (Cout == 1);

  cover property (sum5 == 5'h00);  // 0+0+0
  cover property (sum5 == 5'h10);  // carry-only case (e.g., 8+8+0)
  cover property (sum5 == 5'h1F);  // 15+15+1

  // Specific interesting vectors
  cover property ({A,B,Cin} == {4'h0,4'h0,1'b0});
  cover property ({A,B,Cin} == {4'hF,4'hF,1'b1});
  // Full propagate through all bits (carry ripples from bit0 to Cout)
  cover property (Cin==0 && (A[0]&B[0]) && (A[1]^B[1]) && (A[2]^B[2]) && (A[3]^B[3]) && Cout);

endmodule

// Example bind (put in TB):
// bind four_bit_adder four_bit_adder_sva u_sva (.*);  // if clk,rst_n are in scope
// or explicitly connect:
// bind four_bit_adder four_bit_adder_sva u_sva (.clk(tb_clk), .rst_n(tb_rst_n),
//                                               .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout));