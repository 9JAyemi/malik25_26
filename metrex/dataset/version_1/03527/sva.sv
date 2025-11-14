// SVA for full_adder and adder4 (bind from your TB and connect a sampling clock)

module full_adder_sva(
  input logic clk,
  input logic A, B, Cin,
  input logic S, Cout
);
  default clocking cb @(posedge clk); endclocking

  // No X/Z on interface
  a_no_x: assert property (!$isunknown({A,B,Cin,S,Cout}))
           else $error("full_adder X/Z on interface A=%b B=%b Cin=%b S=%b Cout=%b",A,B,Cin,S,Cout);

  // Functional equivalence
  a_sum_ok: assert property ({Cout,S} == ({1'b0,A}+{1'b0,B}+{1'b0,Cin}))
             else $error("full_adder mismatch A=%0b B=%0b Cin=%0b -> S=%0b Cout=%0b",
                         A,B,Cin,S,Cout);

  // Input space coverage (all 8 combinations)
  c_000: cover property ({A,B,Cin}==3'b000);
  c_001: cover property ({A,B,Cin}==3'b001);
  c_010: cover property ({A,B,Cin}==3'b010);
  c_011: cover property ({A,B,Cin}==3'b011);
  c_100: cover property ({A,B,Cin}==3'b100);
  c_101: cover property ({A,B,Cin}==3'b101);
  c_110: cover property ({A,B,Cin}==3'b110);
  c_111: cover property ({A,B,Cin}==3'b111);
endmodule


module adder4_sva(
  input logic clk,
  input logic [3:0] A, B, S,
  input logic Cout
);
  default clocking cb @(posedge clk); endclocking

  // No X/Z on interface
  a_no_x: assert property (!$isunknown({A,B,S,Cout}))
           else $error("adder4 X/Z on interface A=%h B=%h S=%h Cout=%b",A,B,S,Cout);

  // End-to-end functional equivalence
  a_sum_ok: assert property ({Cout,S} == ({1'b0,A}+{1'b0,B}))
             else $error("adder4 mismatch A=%0h B=%0h -> S=%0h Cout=%0b",A,B,S,Cout);

  // Bitwise ripple-chain checks (pinpointing errors)
  wire c1, c2, c3, c4;
  assign c1 = (A[0] & B[0]);
  assign c2 = (A[1] & B[1]) | ((A[1]^B[1]) & c1);
  assign c3 = (A[2] & B[2]) | ((A[2]^B[2]) & c2);
  assign c4 = (A[3] & B[3]) | ((A[3]^B[3]) & c3);

  a_s0: assert property (S[0] == (A[0]^B[0]))
         else $error("adder4 S[0] mismatch A[0]=%b B[0]=%b S[0]=%b",A[0],B[0],S[0]);
  a_s1: assert property (S[1] == (A[1]^B[1]^c1))
         else $error("adder4 S[1] mismatch");
  a_s2: assert property (S[2] == (A[2]^B[2]^c2))
         else $error("adder4 S[2] mismatch");
  a_s3: assert property (S[3] == (A[3]^B[3]^c3))
         else $error("adder4 S[3] mismatch");
  a_co: assert property (Cout == c4)
         else $error("adder4 Cout mismatch");

  // Concise but meaningful coverage
  c_zero:      cover property (A==4'h0 && B==4'h0 && S==4'h0 && Cout==1'b0);
  c_overflow:  cover property (Cout==1'b1);
  c_maxmax:    cover property (A==4'hF && B==4'hF && Cout==1'b1 && S==4'hE);
  c_full_rpl:  cover property (A==4'hF && B==4'h1 && Cout==1'b1 && S==4'h0);
  c_nocarry:   cover property (((A & B)==4'h0) && (Cout==1'b0) && (S==(A^B)));
endmodule

// Example bind (replace tb_clk with your environment clock signal):
// bind full_adder full_adder_sva u_full_adder_sva (.clk(tb_clk), .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout));
// bind adder4     adder4_sva     u_adder4_sva     (.clk(tb_clk), .A(A), .B(B), .S(S), .Cout(Cout));