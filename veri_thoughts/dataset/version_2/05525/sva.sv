module add_sub_pipeline_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic sub,
    input logic [31:0] sum
);

    // In add mode, sum matches 32-bit addition.
    check_add_mode_function: assert property (
        @($global_clock) (!sub) |-> (sum == (a + b))
    );

    // In subtract mode, sum matches 32-bit subtraction.
    check_sub_mode_function: assert property (
        @($global_clock) sub |-> (sum == (a - b))
    );

    // The low 16 bits in add mode come from the low adder stage.
    check_add_low_half: assert property (
        @($global_clock) (!sub) |-> (sum[15:0] == (a[15:0] + b[15:0]))
    );

    // The high 16 bits in add mode include carry from the low stage.
    check_add_high_half_carry: assert property (
        @($global_clock) (!sub) |-> (
            sum[31:16] == (a[31:16] + b[31:16] + (({1'b0, a[15:0]} + {1'b0, b[15:0]})[16]))
        )
    );

    // The low 16 bits in subtract mode use inverted b and carry_in of 1.
    check_sub_low_half_twos_complement: assert property (
        @($global_clock) sub |-> (
            sum[15:0] == (a[15:0] + (~b[15:0]) + 16'd1)
        )
    );

    // The high 16 bits in subtract mode include carry from the low stage.
    check_sub_high_half_carry: assert property (
        @($global_clock) sub |-> (
            sum[31:16] == (a[31:16] + (~b[31:16]) + (({1'b0, a[15:0]} + {1'b0, (~b[15:0])} + 17'd1)[16]))
        )
    );

    // Adding zero leaves a unchanged.
    check_add_zero_b_passthrough: assert property (
        @($global_clock) ((!sub) && (b == 32'h0000_0000)) |-> (sum == a)
    );

    // Subtracting zero leaves a unchanged.
    check_sub_zero_b_passthrough: assert property (
        @($global_clock) (sub && (b == 32'h0000_0000)) |-> (sum == a)
    );

    // Zero plus b returns b in add mode.
    check_add_zero_a_passthrough: assert property (
        @($global_clock) ((!sub) && (a == 32'h0000_0000)) |-> (sum == b)
    );

    // Subtracting equal operands yields zero.
    check_self_subtract_zero: assert property (
        @($global_clock) (sub && (a == b)) |-> (sum == 32'h0000_0000)
    );

endmodule