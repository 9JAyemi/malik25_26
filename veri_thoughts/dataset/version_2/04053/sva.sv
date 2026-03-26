module top_module_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        sub,
    input logic [31:0] sum
);

    // Sum matches the add/subtract datapath function.
    check_functional_equivalence: assert property (
        @($global_clock) sum == (a + (sub ? ~b : b) + {{31{1'b0}}, sub})
    );

    // In add mode, the result is a + b.
    check_add_mode: assert property (
        @($global_clock) !sub |-> (sum == (a + b))
    );

    // In subtract mode, the result is a - b.
    check_sub_mode: assert property (
        @($global_clock) sub |-> (sum == (a - b))
    );

    // The least significant sum bit is always a[0] XOR b[0].
    check_lsb_xor: assert property (
        @($global_clock) sum[0] == (a[0] ^ b[0])
    );

    // Subtracting equal operands yields zero.
    check_equal_operands_subtract_zero: assert property (
        @($global_clock) (sub && (a == b)) |-> (sum == 32'h00000000)
    );

    // A zero b operand passes a through in both modes.
    check_zero_b_passthrough: assert property (
        @($global_clock) (b == 32'h00000000) |-> (sum == a)
    );

    // With a equal to zero in add mode, the result is b.
    check_zero_a_add_mode: assert property (
        @($global_clock) (!sub && (a == 32'h00000000)) |-> (sum == b)
    );

    // With a equal to zero in subtract mode, the result is two's complement of b.
    check_zero_a_sub_mode: assert property (
        @($global_clock) (sub && (a == 32'h00000000)) |-> (sum == (~b + 32'h00000001))
    );

    // Zero minus or plus zero yields zero.
    check_zero_operands_zero_sum: assert property (
        @($global_clock) ((a == 32'h00000000) && (b == 32'h00000000)) |-> (sum == 32'h00000000)
    );

    // Adding complementary operands yields all ones.
    check_add_complement_all_ones: assert property (
        @($global_clock) (!sub && (a == ~b)) |-> (sum == 32'hFFFFFFFF)
    );

endmodule