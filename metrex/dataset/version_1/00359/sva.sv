// SVA for four_bit_adder and full_adder (concise, high-quality checks + focused coverage)

module four_bit_adder_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [3:0] C,
  input  logic       overflow,
  input  logic [3:0] sum,    // internal
  input  logic [3:0] carry   // internal
);
  always_comb begin
    if (!$isunknown({A,B})) begin
      // No X/Z on outputs/internals when inputs are clean
      assert (!$isunknown({C,overflow,sum,carry})) else $error("four_bit_adder: X/Z on outputs/internals with clean inputs");

      // Top-level functional equivalence (unsigned add)
      assert ({overflow, C} == ({1'b0, A} + {1'b0, B})) else $error("four_bit_adder: {overflow,C} != A+B");

      // Structural consistency
      assert (C == sum) else $error("four_bit_adder: C != sum");

      // Bitwise adder equations (including Cin=0 at bit 0)
      assert (sum[0]    == (A[0]^B[0])) else $error("four_bit_adder: sum[0] mismatch");
      assert (carry[0]  == (A[0]&B[0])) else $error("four_bit_adder: carry[0] mismatch");

      assert (sum[1]    == (A[1]^B[1]) ^ carry[0]) else $error("four_bit_adder: sum[1] mismatch");
      assert (carry[1]  == (A[1]&B[1]) | ((A[1]^B[1]) & carry[0])) else $error("four_bit_adder: carry[1] mismatch");

      assert (sum[2]    == (A[2]^B[2]) ^ carry[1]) else $error("four_bit_adder: sum[2] mismatch");
      assert (carry[2]  == (A[2]&B[2]) | ((A[2]^B[2]) & carry[1])) else $error("four_bit_adder: carry[2] mismatch");

      assert (sum[3]    == (A[3]^B[3]) ^ carry[2]) else $error("four_bit_adder: sum[3] mismatch");
      assert (overflow  == (A[3]&B[3]) | ((A[3]^B[3]) & carry[2])) else $error("four_bit_adder: overflow mismatch");

      // Focused functional coverage (clean inputs only)
      cover (A==4'h0 && B==4'h0 && C==4'h0 && overflow==1'b0);                 // zero + zero
      cover (A==4'hF && B==4'hF && C==4'hE && overflow==1'b1);                 // max + max
      cover (A==4'hF && B==4'h1 && C==4'h0 && overflow==1'b1);                 // full ripple (carry across all bits)
      cover ((A^B)==4'hF && overflow==1'b0);                                    // pure propagate, no generate
      cover (carry[0] && !carry[1]);                                            // single-bit carry generate only
      cover (carry[0] && carry[1] && carry[2] && overflow);                     // multi-stage propagate to overflow
      cover ((A[3]&B[3]) && !carry[2] && overflow);                             // MSB generate w/o incoming carry
    end
  end
endmodule

module full_adder_sva (
  input logic A,
  input logic B,
  input logic Cin,
  input logic S,
  input logic Cout
);
  always_comb begin
    if (!$isunknown({A,B,Cin})) begin
      assert (S    == (A ^ B ^ Cin)) else $error("full_adder: S != A^B^Cin");
      assert (Cout == ((A & B) | (Cin & (A ^ B)))) else $error("full_adder: Cout mismatch");
      assert (!$isunknown({S,Cout})) else $error("full_adder: X/Z on outputs with clean inputs");

      // Focused leaf coverage
      cover (Cin==1'b0 && (A&B));                 // generate (no Cin)
      cover (Cin==1'b1 && (A^B) && !(A&B));       // propagate with Cin
      cover (Cin==1'b1 && (A&B));                 // generate with Cin
      cover (Cin==1'b0 && !(A^B));                // no-carry case
    end
  end
endmodule

bind four_bit_adder four_bit_adder_sva (.A(A), .B(B), .C(C), .overflow(overflow), .sum(sum), .carry(carry));
bind full_adder     full_adder_sva     (.*);