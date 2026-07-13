module add4bit_assertions (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic [4:0]  SUM
);

    // SUM is the zero-extended 4-bit result of A+B.
    check_sum_zero_extended_truncated_add: assert property (
        @(posedge clk) SUM == {1'b0, (A + B)}
    );

    // The upper bit is never set by this implementation.
    check_sum_msb_always_zero: assert property (
        @(posedge clk) SUM[4] == 1'b0
    );

    // The low nibble matches the truncated 4-bit addition.
    check_sum_low_nibble_matches_add: assert property (
        @(posedge clk) SUM[3:0] == (A + B)
    );

    // If the full mathematical sum fits in 4 bits, SUM matches it exactly.
    check_no_overflow_matches_full_sum: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B}) <= 5'd15) |-> (SUM == ({1'b0, A} + {1'b0, B}))
    );

    // If the full mathematical sum exceeds 15, SUM wraps to the low nibble with no carry bit.
    check_overflow_wraps_without_carry: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B}) > 5'd15) |-> (SUM[4] == 1'b0 && SUM[3:0] == (A + B))
    );

    // Stable inputs keep the output stable across sampled cycles.
    check_stable_inputs_imply_stable_sum: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(SUM)
    );

endmodule