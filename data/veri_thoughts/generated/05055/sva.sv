module calculator_sva (
    input logic clk,
    input logic op,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] result,
    input logic carry
);

    // Result matches the selected add or subtract operation.
    check_result_matches_selected_operation: assert property (
        @(posedge clk) result == (op ? (a - b) : (a + b))
    );

    // Carry is asserted only for overflow during addition.
    check_carry_matches_add_overflow: assert property (
        @(posedge clk) carry == ((op == 1'b0) && (({1'b0, a} + {1'b0, b}) > 5'd15))
    );

    // In add mode, the outputs match the full 5-bit sum.
    check_add_outputs_match_sum: assert property (
        @(posedge clk) (op == 1'b0) |-> ({carry, result} == ({1'b0, a} + {1'b0, b}))
    );

    // In subtract mode, result matches the 4-bit difference.
    check_subtract_result_matches_difference: assert property (
        @(posedge clk) (op == 1'b1) |-> (result == (a - b))
    );

    // In subtract mode, carry is always low.
    check_subtract_carry_is_zero: assert property (
        @(posedge clk) (op == 1'b1) |-> (carry == 1'b0)
    );

endmodule