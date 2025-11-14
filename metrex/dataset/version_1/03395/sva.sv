// SVA checker for adder_8bit. Bind this to the DUT.
// Focuses on functional correctness (8-bit modulo addition), X-prop, and key corner cases.

module adder_8bit_sva (
  input logic [7:0] A,
  input logic [7:0] B,
  input logic [7:0] sum
);

  // Core functional checks (combinational, 0-delay)
  always @* begin
    if (!$isunknown({A,B})) begin
      assert (!$isunknown(sum))
        else $error("adder_8bit: sum has X/Z when A,B are known. A=%0h B=%0h sum=%0h", A,B,sum);

      // Correct 8-bit modulo addition
      assert (sum == (A + B)[7:0])
        else $error("adder_8bit: sum != (A+B) mod 256. A=%0h B=%0h sum=%0h exp=%0h",
                    A,B,sum,(A+B)[7:0]);

      // Commutativity (redundant functionally, but catches asymmetric wiring)
      assert (sum == (B + A)[7:0])
        else $error("adder_8bit: non-commutative behavior. A=%0h B=%0h sum=%0h", A,B,sum);

      // LSB must be XOR of inputs (carry-in to bit0 is 0)
      assert (sum[0] == (A[0] ^ B[0]))
        else $error("adder_8bit: LSB incorrect. A0=%0b B0=%0b sum0=%0b", A[0],B[0],sum[0]);

      // Identity with zero
      if (A == 8'h00) assert (sum == B)
        else $error("adder_8bit: 0 + B != B. B=%0h sum=%0h", B,sum);
      if (B == 8'h00) assert (sum == A)
        else $error("adder_8bit: A + 0 != A. A=%0h sum=%0h", A,sum);
    end
  end

  // Corner-case functional coverage
  always @* begin
    cover (!$isunknown({A,B,sum}) && (A==8'h00) && (B==8'h00) && (sum==8'h00)); // zero+zero
    cover (!$isunknown({A,B,sum}) && (A==8'hFF) && (B==8'h01) && (sum==8'h00)); // wrap-around
    cover (!$isunknown({A,B,sum}) && (A==8'h7F) && (B==8'h01) && (sum==8'h80)); // carry into MSB
    cover (!$isunknown({A,B,sum}) && (A==8'h55) && (B==8'hAA) && (sum==8'hFF)); // alternating bits
    cover (!$isunknown({A,B,sum}) && (A==8'h80) && (B==8'h80) && (sum==8'h00)); // MSB+MSB wrap
    cover (!$isunknown({A,B,sum}) && (A==8'h00) && (sum==B));                   // identity A=0
    cover (!$isunknown({A,B,sum}) && (B==8'h00) && (sum==A));                   // identity B=0
  end

endmodule

bind adder_8bit adder_8bit_sva adder_8bit_sva_i (.A(A), .B(B), .sum(sum));