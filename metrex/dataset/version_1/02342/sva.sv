// SVA for full_adder
module full_adder_sva(input a, b, c_in, s, c_out);

  // Functional equivalence
  assert property (@(a or b or c_in) 1'b1 |-> ##0 (s == (a ^ b ^ c_in)));
  assert property (@(a or b or c_in) 1'b1 |-> ##0 (c_out == ((a & b) | (b & c_in) | (c_in & a))));

  // Knownness: if inputs known, outputs known
  assert property (@(a or b or c_in) (!$isunknown({a,b,c_in})) |-> ##0 (!$isunknown({s,c_out})));

  // Coverage
  cover property (@(a or b or c_in) ##0 s);
  cover property (@(a or b or c_in) ##0 !s);
  cover property (@(a or b or c_in) ##0 c_out);
  cover property (@(a or b or c_in) ##0 !c_out);
  cover property (@(a or b or c_in) ##0 (c_out && (a & b))); // generate
  cover property (@(a or b or c_in) ##0 (c_out && !(a & b) && ((b & c_in) | (c_in & a)))); // propagate

endmodule

bind full_adder full_adder_sva i_full_adder_sva(.a(a), .b(b), .c_in(c_in), .s(s), .c_out(c_out));


// SVA for four_bit_adder (binds to internal carries)
module four_bit_adder_sva(
  input [3:0] A, B, S,
  input C_in, C_out,
  input c1, c2, c3
);

  // End-to-end arithmetic correctness
  assert property (@(A or B or C_in) 1'b1 |-> ##0 ({C_out, S} == (A + B + C_in)));

  // Bitwise sum and carry chain
  assert property (@(A[0] or B[0] or C_in) 1'b1 |-> ##0 (S[0] == (A[0]^B[0]^C_in)));
  assert property (@(A[0] or B[0] or C_in) 1'b1 |-> ##0 (c1   == ((A[0]&B[0]) | (B[0]&C_in) | (C_in&A[0]))));

  assert property (@(A[1] or B[1] or c1) 1'b1 |-> ##0 (S[1] == (A[1]^B[1]^c1)));
  assert property (@(A[1] or B[1] or c1) 1'b1 |-> ##0 (c2   == ((A[1]&B[1]) | (B[1]&c1) | (c1&A[1]))));

  assert property (@(A[2] or B[2] or c2) 1'b1 |-> ##0 (S[2] == (A[2]^B[2]^c2)));
  assert property (@(A[2] or B[2] or c2) 1'b1 |-> ##0 (c3   == ((A[2]&B[2]) | (B[2]&c2) | (c2&A[2]))));

  assert property (@(A[3] or B[3] or c3) 1'b1 |-> ##0 (S[3]   == (A[3]^B[3]^c3)));
  assert property (@(A[3] or B[3] or c3) 1'b1 |-> ##0 (C_out == ((A[3]&B[3]) | (B[3]&c3) | (c3&A[3]))));

  // Derived property: MSB generate forces carry out
  assert property (@(A[3] or B[3]) (A[3] & B[3]) |-> ##0 C_out);

  // Knownness: if inputs known, outputs known
  assert property (@(A or B or C_in) (!$isunknown({A,B,C_in})) |-> ##0 (!$isunknown({S,C_out})));

  // Coverage
  wire [3:0] P = A ^ B;

  cover property (@(A or B or C_in) ##0 C_out);
  cover property (@(A or B or C_in) ##0 !C_out);

  // Full propagate chain cases
  cover property (@(A or B or C_in) (P == 4'hF && C_in == 1'b0) ##0 (!C_out));
  cover property (@(A or B or C_in) (P == 4'hF && C_in == 1'b1) ##0 (C_out));

  // Observe long carry chain inside
  cover property (@(A or B or C_in) ##0 (c1 && c2 && c3));

endmodule

bind four_bit_adder four_bit_adder_sva i_four_bit_adder_sva(
  .A(A), .B(B), .C_in(C_in), .S(S), .C_out(C_out), .c1(c1), .c2(c2), .c3(c3)
);