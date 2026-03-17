module four_bit_adder_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        CI,
    input logic [3:0]  SUM,
    input logic        COUT
);

    // SUM is the bitwise XOR of A and B.
    check_sum_matches_bitwise_xor: assert property (
        @(posedge clk) SUM == (A ^ B)
    );

    // COUT matches the arithmetic carry-out of A + B + CI.
    check_cout_matches_arithmetic_carry: assert property (
        @(posedge clk) COUT == (({1'b0, A} + {1'b0, B} + {4'b0, CI}) >= 5'd16)
    );

    // Changing CI alone does not change SUM.
    check_sum_ignores_carry_in_changes: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $changed(CI)) |-> $stable(SUM)
    );

    // Equal operands force all SUM bits low.
    check_equal_operands_force_zero_sum: assert property (
        @(posedge clk) (A == B) |-> (SUM == 4'b0000)
    );

    // Complementary operands force all SUM bits high and propagate CI to COUT.
    check_complementary_operands_propagate_carry: assert property (
        @(posedge clk) (A == ~B) |-> ((SUM == 4'b1111) && (COUT == CI))
    );

    // Zero operands clear both SUM and COUT.
    check_zero_operands_clear_outputs: assert property (
        @(posedge clk) (A == 4'b0000 && B == 4'b0000) |-> ((SUM == 4'b0000) && (COUT == 1'b0))
    );

    // All-one operands force zero SUM and a asserted carry-out.
    check_all_ones_operands_generate_carry: assert property (
        @(posedge clk) (A == 4'b1111 && B == 4'b1111) |-> ((SUM == 4'b0000) && (COUT == 1'b1))
    );

endmodule