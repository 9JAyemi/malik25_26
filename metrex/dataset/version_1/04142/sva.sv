// Bindable SVA for four_bit_adder
module four_bit_adder_sva(
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [3:0] S,
  input  logic       Cout,
  input  logic [3:0] C
);
  always_comb begin
    automatic logic [4:0] sum5 = {1'b0, A} + {1'b0, B};

    if (!$isunknown({A,B})) begin
      // Functional correctness
      assert ({Cout, S} === sum5)
        else $error("Adder mismatch: A=%0h B=%0h S=%0h Cout=%0b exp_sum=%0h", A, B, S, Cout, sum5);

      // Internal wire C width/concatenation check
      assert (C === {1'b0, A[3], B[3], S[3]})
        else $error("Internal C mismatch: C=%b exp=%b", C, {1'b0, A[3], B[3], S[3]});

      // Coverage (key corners and behaviors)
      cover (Cout == 0);
      cover (Cout == 1);
      cover (A == 4'h0 && B == 4'h0);            // zero + zero
      cover (A == 4'hF && B == 4'h0);            // max + zero
      cover (A == 4'h0 && B == 4'hF);            // zero + max
      cover (A == 4'hF && B == 4'h1);            // overflow by 1
      cover (S == 4'h0 && Cout == 1'b1);         // wrap to zero with carry
      cover (S == 4'h0 && Cout == 1'b0);         // exact zero
      cover (A == B);                             // symmetry case
      cover (sum5[3:0] == 4'hF);                  // boundary sum
    end
  end
endmodule

// Bind into the DUT
bind four_bit_adder four_bit_adder_sva sva_i(.A(A), .B(B), .S(S), .Cout(Cout), .C(C));