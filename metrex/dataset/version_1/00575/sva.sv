// SVA for adder_4bit and full_adder
// Concise, bindable, with key correctness checks and targeted coverage

// Top-level checker bound into adder_4bit (references internal C[2:0])
module adder_4bit_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [3:0] S,
  input  logic       C_out,
  input  logic [3:0] C   // only [2:0] are used
);
  // Golden functional equivalence (5-bit sum)
  assert property (@(A or B or S or C_out)
                   disable iff ($isunknown({A,B}))
                   {C_out,S} == A + B);

  // No X/Z on outputs when inputs are known
  assert property (@(A or B or S or C_out or C)
                   !$isunknown({A,B}) |-> !$isunknown({S,C_out,C[2:0]}));

  // Bit 0 stage (C_in=0)
  assert property (@(A or B or S or C)
                   disable iff ($isunknown({A,B}))
                   S[0] == (A[0]^B[0]));
  assert property (@(A or B or C)
                   disable iff ($isunknown({A,B}))
                   C[0] == (A[0]&B[0]));

  // Ripple stages 1..2
  assert property (@(A or B or S or C)
                   disable iff ($isunknown({A,B}))
                   S[1] == (A[1]^B[1]^C[0]));
  assert property (@(A or B or C)
                   disable iff ($isunknown({A,B}))
                   C[1] == ((A[1]&B[1]) | (C[0]&(A[1]^B[1]))));

  assert property (@(A or B or S or C)
                   disable iff ($isunknown({A,B}))
                   S[2] == (A[2]^B[2]^C[1]));
  assert property (@(A or B or C)
                   disable iff ($isunknown({A,B}))
                   C[2] == ((A[2]&B[2]) | (C[1]&(A[2]^B[2]))));

  // MSB stage and final carry
  assert property (@(A or B or S or C or C_out)
                   disable iff ($isunknown({A,B}))
                   S[3] == (A[3]^B[3]^C[2]));
  assert property (@(A or B or C or C_out)
                   disable iff ($isunknown({A,B}))
                   C_out == ((A[3]&B[3]) | (C[2]&(A[3]^B[3]))));

  // Sanity corner cases
  assert property (@(A or B or S or C_out)
                   disable iff ($isunknown({A,B}))
                   (B==4'b0) |-> (S==A && !C_out));
  assert property (@(A or B or S or C_out)
                   disable iff ($isunknown({A,B}))
                   (A==4'b0) |-> (S==B && !C_out));

  // Coverage: overflow and no-overflow seen
  cover property (@(A or B) !$isunknown({A,B}) && (A+B > 4'hF) && C_out);
  cover property (@(A or B) !$isunknown({A,B}) && (A+B <= 4'hF) && !C_out);

  // Coverage: internal carries exercised
  cover property (@(A or B) !$isunknown({A,B}) && C[0]);
  cover property (@(A or B) !$isunknown({A,B}) && C[1]);
  cover property (@(A or B) !$isunknown({A,B}) && C[2]);

  // Coverage: 3-bit ripple propagation across stages (0->1 carry ripples through 1,2,3)
  cover property (@(A or B)
    !$isunknown({A,B}) &&
    (A[0]&B[0]) && (A[1]^B[1]) && (A[2]^B[2]) && (A[3]^B[3]) && C_out);
endmodule

// Checker bound into each full_adder instance
module full_adder_sva (
  input logic A,
  input logic B,
  input logic C_in,
  input logic S,
  input logic C_out
);
  // Truth-equations
  assert property (@(A or B or C_in or S)
                   disable iff ($isunknown({A,B,C_in}))
                   S == (A^B^C_in));
  assert property (@(A or B or C_in or C_out)
                   disable iff ($isunknown({A,B,C_in}))
                   C_out == ((A&B) | (C_in&(A^B))));

  // Outputs known when inputs known
  assert property (@(A or B or C_in or S or C_out)
                   !$isunknown({A,B,C_in}) |-> !$isunknown({S,C_out}));

  // Coverage: generate, propagate, and kill scenarios
  cover property (@(A or B or C_in) !C_in && (A&B) && C_out);              // generate
  cover property (@(A or B or C_in)  C_in && (A^B) && C_out);              // propagate
  cover property (@(A or B or C_in)  C_in && !(A|B) && !C_out);            // kill
endmodule

// Example binds (use in your TB or a bind file)
// bind adder_4bit  adder_4bit_sva  u_adder_4bit_sva (.A(A),.B(B),.S(S),.C_out(C_out),.C(C));
// bind full_adder  full_adder_sva  u_full_adder_sva (.*);