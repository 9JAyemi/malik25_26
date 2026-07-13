module RippleCarryAdder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       CIN,
    input logic [3:0] S,
    input logic       COUT
);

    // Sampling clock: clk.
    // Reset: none in RTL.
    // DUT is a combinational 4-bit ripple-carry adder.

    // Full 5-bit result matches A + B + CIN.
    check_total_sum: assert property (
        @(posedge clk)
        {COUT, S} == ({1'b0, A} + {1'b0, B} + CIN)
    );

    // Bit 0 sum matches the first full adder.
    check_bit0_sum: assert property (
        @(posedge clk)
        S[0] == (A[0] ^ B[0] ^ CIN)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk)
        S[1] == (
            A[1] ^ B[1] ^
            ((A[0] & B[0]) | ((A[0] ^ B[0]) & CIN))
        )
    );

    // Bit 2 sum uses the carry from bit 1.
    check_bit2_sum: assert property (
        @(posedge clk)
        S[2] == (
            A[2] ^ B[2] ^
            (
                (A[1] & B[1]) |
                ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & CIN)))
            )
        )
    );

    // Bit 3 sum uses the carry from bit 2.
    check_bit3_sum: assert property (
        @(posedge clk)
        S[3] == (
            A[3] ^ B[3] ^
            (
                (A[2] & B[2]) |
                ((A[2] ^ B[2]) & (
                    (A[1] & B[1]) |
                    ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & CIN)))
                ))
            )
        )
    );

    // Final carry-out matches the last full adder.
    check_final_carry: assert property (
        @(posedge clk)
        COUT == (
            (A[3] & B[3]) |
            ((A[3] ^ B[3]) & (
                (A[2] & B[2]) |
                ((A[2] ^ B[2]) & (
                    (A[1] & B[1]) |
                    ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & CIN)))
                ))
            ))
        )
    );

    // Adding zero on B with no carry-in returns A.
    check_add_zero_on_b: assert property (
        @(posedge clk)
        ((B == 4'h0) && (CIN == 1'b0)) |-> ({COUT, S} == {1'b0, A})
    );

    // Adding zero on A with no carry-in returns B.
    check_add_zero_on_a: assert property (
        @(posedge clk)
        ((A == 4'h0) && (CIN == 1'b0)) |-> ({COUT, S} == {1'b0, B})
    );

    // Zero operands reduce the result to the carry-in.
    check_zero_operands_cin_only: assert property (
        @(posedge clk)
        ((A == 4'h0) && (B == 4'h0)) |-> ({COUT, S} == {4'h0, CIN})
    );

endmodule