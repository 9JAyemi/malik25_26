module ripple_carry_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Ci,
    input logic [3:0] S,
    input logic       Co
);

    // The 5-bit output matches the 5-bit arithmetic sum.
    check_total_sum: assert property (
        @(posedge clk) {Co, S} == ({1'b0, A} + {1'b0, B} + Ci)
    );

    // The least-significant sum bit is the XOR of A[0], B[0], and Ci.
    check_lsb_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Ci)
    );

    // Adding zero with no carry-in returns A with no carry-out.
    check_add_zero_to_a: assert property (
        @(posedge clk) (B == 4'h0 && Ci == 1'b0) |-> (S == A && Co == 1'b0)
    );

    // Adding zero with no carry-in returns B with no carry-out.
    check_add_zero_to_b: assert property (
        @(posedge clk) (A == 4'h0 && Ci == 1'b0) |-> (S == B && Co == 1'b0)
    );

    // A carry-in by itself increments zero to one without overflow.
    check_carry_in_only: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0 && Ci == 1'b1) |-> (S == 4'h1 && Co == 1'b0)
    );

    // A carry-in propagates through all four stages when A is all ones.
    check_full_carry_propagation: assert property (
        @(posedge clk) (A == 4'hF && B == 4'h0 && Ci == 1'b1) |-> (S == 4'h0 && Co == 1'b1)
    );

    // Carry-out stays low when the arithmetic sum fits in 4 bits.
    check_no_overflow_when_sum_fits: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + Ci) <= 5'd15) |-> (Co == 1'b0)
    );

    // Carry-out goes high when the arithmetic sum exceeds 4 bits.
    check_overflow_when_sum_exceeds: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + Ci) >= 5'd16) |-> (Co == 1'b1)
    );

endmodule