// SVA checkers for half_adder and full_adder
// Clocked, concise, and focused on functional correctness and X-safety.

module ha_sva (
  input logic clk,
  input logic rst_n,
  input logic a,
  input logic b,
  input logic sum,
  input logic carry
);
  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional correctness + X-safety when inputs are known
  assert property ( !$isunknown({a,b}) |-> (!$isunknown({sum,carry}) &&
                                            sum   == (a ^ b) &&
                                            carry == (a & b)) );

  // Coverage: all 4 input/output combinations
  cover property (!$isunknown({a,b,sum,carry}) && {a,b,sum,carry} == 4'b0000); // 0+0 -> 0,0
  cover property (!$isunknown({a,b,sum,carry}) && {a,b,sum,carry} == 4'b0101); // 0+1 -> 1,0
  cover property (!$isunknown({a,b,sum,carry}) && {a,b,sum,carry} == 4'b1001); // 1+0 -> 1,0
  cover property (!$isunknown({a,b,sum,carry}) && {a,b,sum,carry} == 4'b1110); // 1+1 -> 0,1
endmodule


module fa_sva (
  input logic clk,
  input logic rst_n,
  input logic A,
  input logic B,
  input logic Cin,
  input logic S,
  input logic Cout
);
  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional correctness (3-input full adder) + X-safety when inputs known
  assert property ( !$isunknown({A,B,Cin}) |-> (!$isunknown({S,Cout}) &&
                                               S    == (A ^ B ^ Cin) &&
                                               Cout == ((A & B) | (A & Cin) | (B & Cin)) ) );

  // Coverage: all 8 input/output combinations
  cover property (!$isunknown({A,B,Cin,S,Cout}) && {A,B,Cin,S,Cout} == 5'b00000);
  cover property (!$isunknown({A,B,Cin,S,Cout}) && {A,B,Cin,S,Cout} == 5'b00110);
  cover property (!$isunknown({A,B,Cin,S,Cout}) && {A,B,Cin,S,Cout} == 5'b01010);
  cover property (!$isunknown({A,B,Cin,S,Cout}) && {A,B,Cin,S,Cout} == 5'b01101);
  cover property (!$isunknown({A,B,Cin,S,Cout}) && {A,B,Cin,S,Cout} == 5'b10010);
  cover property (!$isunknown({A,B,Cin,S,Cout}) && {A,B,Cin,S,Cout} == 5'b10101);
  cover property (!$isunknown({A,B,Cin,S,Cout}) && {A,B,Cin,S,Cout} == 5'b11001);
  cover property (!$isunknown({A,B,Cin,S,Cout}) && {A,B,Cin,S,Cout} == 5'b11110);
endmodule


// Optional: structural checks of the two-half-adder decomposition inside full_adder
module fa_int_sva (
  input logic clk,
  input logic rst_n,
  input logic A, B, Cin,
  input logic S, Cout,
  input logic sum1, carry1, sum2, carry2
);
  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Check each half-adder instance behavior and final wiring
  assert property (!$isunknown({A,B})     |-> (sum1   == (A ^ B)   && carry1 == (A & B)));
  assert property (!$isunknown({sum1,Cin})|-> (sum2   == (sum1 ^ Cin) && carry2 == (sum1 & Cin)));
  assert property (S == sum2);
  assert property (Cout == (carry1 | carry2));

  // Coverage: exercise both carry paths
  cover property (!$isunknown({A,B,Cin,carry1,Cout}) && (A & B) && carry1 && Cout);           // carry from first HA
  cover property (!$isunknown({A,B,Cin,carry2,Cout}) && (A ^ B) && Cin && carry2 && Cout);    // carry from second HA
endmodule


// Example bind usage (hook clk/rst_n from your TB):
// bind half_adder ha_sva  u_ha_sva ( .clk(tb_clk), .rst_n(tb_rst_n), .a(a), .b(b), .sum(sum), .carry(carry) );
// bind full_adder fa_sva  u_fa_sva ( .clk(tb_clk), .rst_n(tb_rst_n), .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout) );
// bind full_adder fa_int_sva u_fa_int_sva ( .clk(tb_clk), .rst_n(tb_rst_n),
//                                           .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout),
//                                           .sum1(sum1), .carry1(carry1), .sum2(sum2), .carry2(carry2) );