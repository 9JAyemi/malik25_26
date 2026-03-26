module addsub_8bit_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic       op,
    input logic [7:0] sum,
    input logic       carry_out
);

    // carry_out is hard-wired low.
    check_carry_out_tied_low: assert property (
        @($global_clock) disable iff (1'b0)
        carry_out == 1'b0
    );

    // sum follows the top-level conditional expression.
    check_sum_matches_top_level_function: assert property (
        @($global_clock) disable iff (1'b0)
        sum == (op ? ((~B) + 8'h01) : (A ^ ((~B) + 8'h01)))
    );

    // op high selects the two's complement of B.
    check_sum_equals_twos_comp_b_when_op_high: assert property (
        @($global_clock) disable iff (1'b0)
        (op == 1'b1) |-> (sum == ((~B) + 8'h01))
    );

    // op low selects the XOR path with A and two's complement of B.
    check_sum_equals_xor_path_when_op_low: assert property (
        @($global_clock) disable iff (1'b0)
        (op == 1'b0) |-> (sum == (A ^ ((~B) + 8'h01)))
    );

    // With B equal to zero, op high produces zero.
    check_zero_b_gives_zero_when_op_high: assert property (
        @($global_clock) disable iff (1'b0)
        ((op == 1'b1) && (B == 8'h00)) |-> (sum == 8'h00)
    );

    // With B equal to zero, op low passes A through.
    check_zero_b_passes_a_when_op_low: assert property (
        @($global_clock) disable iff (1'b0)
        ((op == 1'b0) && (B == 8'h00)) |-> (sum == A)
    );

    // With A equal to zero, op low reduces to two's complement of B.
    check_zero_a_reduces_to_twos_comp_b_when_op_low: assert property (
        @($global_clock) disable iff (1'b0)
        ((op == 1'b0) && (A == 8'h00)) |-> (sum == ((~B) + 8'h01))
    );

endmodule