// SVA for four_bit_adder and full_adder
// Bind these into the DUT; immediate assertions check combinational equivalence.

module four_bit_adder_sva(
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] S,
  input  logic       Cout,
  input  logic [3:0] sum,
  input  logic [3:0] carry
);
  // Combinational correctness and X-prop
  always_comb begin
    if (!$isunknown({A,B,Cin})) begin
      logic [4:0] exp = {1'b0,A} + {1'b0,B} + Cin;
      assert ({Cout,S} == exp) else $error("Adder mismatch: A=%0h B=%0h Cin=%0b got {Cout,S}=%0h exp=%0h", A,B,Cin,{Cout,S},exp);

      // Output mirrors internal sum bus
      assert (S === sum) else $error("S != internal sum");

      // Bit-level sum and carry ripple relations
      assert (S[0] == (A[0]^B[0]^Cin));
      assert (carry[0] == ((A[0]&B[0]) | ((A[0]^B[0]) & Cin)));
      assert (S[1] == (A[1]^B[1]^carry[0]));
      assert (carry[1] == ((A[1]&B[1]) | ((A[1]^B[1]) & carry[0])));
      assert (S[2] == (A[2]^B[2]^carry[1]));
      assert (carry[2] == ((A[2]&B[2]) | ((A[2]^B[2]) & carry[1])));
      assert (S[3] == (A[3]^B[3]^carry[2]));
      assert (Cout == ((A[3]&B[3]) | ((A[3]^B[3]) & carry[2])));

      // No X leakage to outputs/internal sums
      assert (!$isunknown({S,Cout,sum,carry})) else $error("X/Z observed on outputs");
    end

    // Functional coverage (immediate covers)
    cover ((A==4'h0)&&(B==4'h0)&&(Cin==1'b0));            // zero + zero
    cover ((A==4'hF)&&(B==4'hF)&&(Cin==1'b1));            // max + max + 1 (Cout=1)
    cover ((&(A^B))&&(Cin==1'b0)&&(Cout==1'b0));          // full propagate, Cin=0
    cover ((&(A^B))&&(Cin==1'b1)&&(Cout==1'b1));          // full propagate, Cin=1
    cover (| (A & B));                                    // any generate
    cover (~| (A | B) && Cin);                            // pure carry-in only
    cover (Cout==1'b0);
    cover (Cout==1'b1);
    cover (S==4'h0);
    cover (S==4'hF);
    cover ((A[3]==B[3]) && (S[3]!=A[3]));                 // signed overflow
    cover (carry[0] && carry[1] && carry[2]);             // ripple through all stages
  end
endmodule

bind four_bit_adder four_bit_adder_sva four_bit_adder_sva_i(.*);

module full_adder_sva(
  input logic A,
  input logic B,
  input logic Cin,
  input logic S,
  input logic Cout,
  input logic sum,
  input logic Cout1,
  input logic Cout2
);
  always_comb begin
    if (!$isunknown({A,B,Cin})) begin
      // Gate-level decomposition equivalence
      assert (sum  == (A ^ B)) else $error("sum != A^B");
      assert (S    == (A ^ B ^ Cin)) else $error("S != A^B^Cin");
      assert (Cout1== (A & B)) else $error("Cout1 != A&B");
      assert (Cout2== ((A ^ B) & Cin)) else $error("Cout2 != (A^B)&Cin");
      assert (Cout == (Cout1 | Cout2)) else $error("Cout != Cout1|Cout2");
      assert (Cout == ((A & B) | ((A ^ B) & Cin))) else $error("Cout formula mismatch");
      assert (!$isunknown({S,Cout,sum,Cout1,Cout2})) else $error("X/Z on outputs");
    end

    // Truth-table coverage for all 8 input combinations
    cover ({A,B,Cin}==3'b000);
    cover ({A,B,Cin}==3'b001);
    cover ({A,B,Cin}==3'b010);
    cover ({A,B,Cin}==3'b011);
    cover ({A,B,Cin}==3'b100);
    cover ({A,B,Cin}==3'b101);
    cover ({A,B,Cin}==3'b110);
    cover ({A,B,Cin}==3'b111);
    cover (Cout==1'b0);
    cover (Cout==1'b1);
    cover (S==1'b0);
    cover (S==1'b1);
  end
endmodule

bind full_adder full_adder_sva full_adder_sva_i(.*);