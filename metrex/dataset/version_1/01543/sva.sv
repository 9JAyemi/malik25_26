// SVA checkers and binds for four_bit_adder and full_adder

// 1-bit full_adder checker (golden equations)
module full_adder_sva_bind (
  input logic A, B, Cin,
  input logic Sum, Cout
);
  always_comb begin
    assert (Sum  == (A ^ B ^ Cin))
      else $error("full_adder Sum mismatch: A=%0b B=%0b Cin=%0b Sum=%0b", A,B,Cin,Sum);
    assert (Cout == ((A & B) | (Cin & (A ^ B))))
      else $error("full_adder Cout mismatch: A=%0b B=%0b Cin=%0b Cout=%0b", A,B,Cin,Cout);

    // Lightweight FA coverage
    cover (A & B);                  // generate
    cover ((A ^ B) & Cin);          // propagate used
    cover ((~A & ~B) & Cin);        // kill carry
    cover ((A ^ B ^ Cin) == 1'b0);  // Sum=0 case
    cover (Cout);                   // carry-out asserted
  end
endmodule

// 4-bit adder checker (end-to-end + internal ripple and xor_sum)
module four_bit_adder_sva_bind (
  input  logic [3:0] A, B,
  input  logic       Cin,
  input  logic [3:0] Sum,
  input  logic       Cout,
  input  logic [3:0] carry,    // bind to internal
  input  logic [3:0] xor_sum   // bind to internal
);
  always_comb begin
    // End-to-end correctness
    assert ({Cout, Sum} == (A + B + Cin))
      else $error("4b adder result mismatch: A=%0h B=%0h Cin=%0b -> Sum=%0h Cout=%0b", A,B,Cin,Sum,Cout);

    // Internal xor_sum correctness
    for (int i=0;i<4;i++) begin
      assert (xor_sum[i] == (A[i] ^ B[i]))
        else $error("xor_sum[%0d] mismatch: A=%0b B=%0b xor_sum=%0b", i, A[i], B[i], xor_sum[i]);
    end

    // Ripple-carry equations per bit
    assert (carry[0] == ((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))))
      else $error("carry[0] mismatch");
    for (int i=1;i<4;i++) begin
      assert (carry[i] == ((A[i] & B[i]) | (carry[i-1] & (A[i] ^ B[i]))))
        else $error("carry[%0d] mismatch", i);
    end

    // Sum bits with proper incoming carry
    assert (Sum[0] == (A[0] ^ B[0] ^ Cin)) else $error("Sum[0] mismatch");
    for (int i=1;i<4;i++) begin
      assert (Sum[i] == (A[i] ^ B[i] ^ carry[i-1])) else $error("Sum[%0d] mismatch", i);
    end

    // Final Cout must equal final ripple carry
    assert (Cout == carry[3]) else $error("Cout != carry[3]");

    // Focused functional coverage
    cover (A==4'h0 && B==4'h0 && Cin==1'b0);      // baseline
    cover (&(A ^ B) && Cin);                      // full propagate chain
    cover (A==4'hF && B==4'hF && Cin==1'b1);      // worst-case overflow
    cover (Sum==4'h0);                             // zero sum
    cover (Cout);                                  // any carry out
  end
endmodule

// Bind the checkers to the DUTs
bind full_adder     full_adder_sva_bind     (.*);
bind four_bit_adder four_bit_adder_sva_bind (.A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout),
                                             .carry(carry), .xor_sum(xor_sum));