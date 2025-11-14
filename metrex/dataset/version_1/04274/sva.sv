// SVA checker for adder4bit and full_adder
// Concise, covers function and structure, and avoids X-propagation

module adder4bit_sva(input [3:0] A, B,
                     input       cin,
                     input [3:0] S,
                     input       cout);

  // Local reconstruction of ripple carries
  logic c0, c1, c2;
  assign c0 = (A[0] & B[0]) | (A[0] & cin) | (B[0] & cin);
  assign c1 = (A[1] & B[1]) | (A[1] & c0 ) | (B[1] & c0 );
  assign c2 = (A[2] & B[2]) | (A[2] & c1 ) | (B[2] & c1 );

  // Functional correctness (5-bit sum)
  assert property (@(A or B or cin)
                   disable iff ($isunknown({A,B,cin}))
                   ##0 {cout,S} == (A + B + cin));

  // Bitwise structure checks (sum XORs and carry equations)
  assert property (@(A or B or cin)
                   disable iff ($isunknown({A,B,cin}))
                   ##0 S[0] == (A[0] ^ B[0] ^ cin));

  assert property (@(A or B or cin)
                   disable iff ($isunknown({A,B,cin}))
                   ##0 S[1] == (A[1] ^ B[1] ^ c0));

  assert property (@(A or B or cin)
                   disable iff ($isunknown({A,B,cin}))
                   ##0 S[2] == (A[2] ^ B[2] ^ c1));

  assert property (@(A or B or cin)
                   disable iff ($isunknown({A,B,cin}))
                   ##0 S[3] == (A[3] ^ B[3] ^ c2));

  assert property (@(A or B or cin)
                   disable iff ($isunknown({A,B,cin}))
                   ##0 cout == ((A[3] & B[3]) | (A[3] & c2) | (B[3] & c2)));

  // No X on outputs when inputs are known
  assert property (@(A or B or cin)
                   disable iff ($isunknown({A,B,cin}))
                   ##0 !$isunknown({S,cout}));

  // Minimal, meaningful coverage
  cover property (@(A or B or cin) disable iff ($isunknown({A,B,cin}))
                  ##0 (A==4'h0 && B==4'h0 && cin==0 && S==4'h0 && cout==0)); // zero

  cover property (@(A or B or cin) disable iff ($isunknown({A,B,cin}))
                  ##0 (A==4'hF && B==4'hF && cin==1 && S==4'hF && cout==1)); // max + carry

  cover property (@(A or B or cin) disable iff ($isunknown({A,B,cin}))
                  ##0 (cout==0));

  cover property (@(A or B or cin) disable iff ($isunknown({A,B,cin}))
                  ##0 (cout==1));

  // Full propagate chain (all bits propagate, incoming carry exits)
  cover property (@(A or B or cin) disable iff ($isunknown({A,B,cin}))
                  ##0 ((A^B)==4'hF && cin==1 && cout==1));
endmodule

bind adder4bit adder4bit_sva sva_top(.A(A), .B(B), .cin(cin), .S(S), .cout(cout));


// Optional: direct checker for the full_adder leaf cell
module full_adder_sva(input a,b,cin, input sum, input cout);
  assert property (@(a or b or cin)
                   disable iff ($isunknown({a,b,cin}))
                   ##0 (sum == (a ^ b ^ cin)) && (cout == ((a & b) | (a & cin) | (b & cin))));

  assert property (@(a or b or cin)
                   disable iff ($isunknown({a,b,cin}))
                   ##0 !$isunknown({sum,cout}));

  // Coverage for generate, propagate, kill
  cover property (@(a or b or cin) ##0 (a&b) && cout);     // generate
  cover property (@(a or b or cin) ##0 (a^b) && cin && cout); // propagate
  cover property (@(a or b or cin) ##0 !(a|b) && !cin && !cout); // kill
endmodule

bind full_adder full_adder_sva fa_chk(.a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));