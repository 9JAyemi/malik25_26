// SVA for two_bit_adder and submodules (concise, quality-focused)
`ifndef TWO_BIT_ADDER_SVA_SV
`define TWO_BIT_ADDER_SVA_SV

// 2-bit adder end-to-end correctness, X-prop checks, and key coverage
module two_bit_adder_sva
  (
    input logic [1:0] A,
    input logic [1:0] B,
    input logic       Cin,
    input logic [1:0] Sum,
    input logic       Cout
  );
  // Functional correctness (3-bit sum)
  assert property (@(A or B or Cin)
    {Cout,Sum} == ({1'b0,A} + {1'b0,B} + Cin)
  );

  // Outputs known when inputs known
  assert property (@(A or B or Cin)
    !$isunknown({A,B,Cin}) |-> !$isunknown({Sum,Cout})
  );

  // Key corner coverage
  cover property (@(A or B or Cin) A==2'b00 && B==2'b00 && Cin==0 && {Cout,Sum}==3'b000);
  cover property (@(A or B or Cin) A==2'b11 && B==2'b11 && Cin==1 && {Cout,Sum}==3'b111);

  // LSB carry generate only (propagate path idle)
  cover property (@(A or B or Cin)
    (A[0]&B[0]) && !Cin && A[1]==0 && B[1]==0 && Cout==0 && Sum[0]==0
  );

  // Carry propagate through MSB
  cover property (@(A or B or Cin)
    (A[0]^B[0]) && Cin && (A[1]^B[1]) && Cout==1
  );

  // MSB kill with incoming carry
  cover property (@(A or B or Cin)
    (((A[0]&B[0]) || ((A[0]^B[0]) && Cin)) && (A[1]==0 && B[1]==0) && Cout==0)
  );

  // MSB generate regardless of incoming carry
  cover property (@(A or B or Cin)
    (A[1]&B[1]) && Cout==1
  );
endmodule

// Full adder local correctness and coverage
module full_adder_sva
  (
    input logic a,
    input logic b,
    input logic cin,
    input logic sum,
    input logic cout
  );
  assert property (@(a or b or cin) sum == (a ^ b ^ cin));
  assert property (@(a or b or cin) cout == ((a & b) | (cin & (a ^ b))));
  assert property (@(a or b or cin) !$isunknown({a,b,cin}) |-> !$isunknown({sum,cout}));

  // Carry generate / propagate / kill coverage + extremes
  cover property (@(a or b or cin) a==0 && b==0 && cin==0 && sum==0 && cout==0);
  cover property (@(a or b or cin) a==1 && b==1 && cin==1 && sum==1 && cout==1);
  cover property (@(a or b or cin) (a&b) && cout==1);                      // generate
  cover property (@(a or b or cin) (cin & (a ^ b)) && ! (a & b) && cout==1); // propagate
  cover property (@(a or b or cin) cin && !(a|b) && cout==0);               // kill
endmodule

// Half adder local correctness and coverage
module half_adder_sva
  (
    input logic a,
    input logic b,
    input logic sum,
    input logic carry
  );
  assert property (@(a or b) sum == (a ^ b));
  assert property (@(a or b) carry == (a & b));
  assert property (@(a or b) !$isunknown({a,b}) |-> !$isunknown({sum,carry}));

  cover property (@(a or b) a==0 && b==0 && sum==0 && carry==0);
  cover property (@(a or b) a==0 && b==1 && sum==1 && carry==0);
  cover property (@(a or b) a==1 && b==0 && sum==1 && carry==0);
  cover property (@(a or b) a==1 && b==1 && sum==0 && carry==1);
endmodule

// Bind the SVA modules to the DUT hierarchy
bind two_bit_adder two_bit_adder_sva i_two_bit_adder_sva (.A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout));
bind full_adder    full_adder_sva    i_full_adder_sva    (.a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));
bind half_adder    half_adder_sva    i_half_adder_sva    (.a(a), .b(b), .sum(sum), .carry(carry));

`endif