module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic       CO
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // Combined outputs must equal the 5-bit sum of A and B.
    check_full_sum: assert property (
        @($global_clock) {CO, C} == ({1'b0, A} + {1'b0, B})
    );

    // Carry-out must be high when the 4-bit sum overflows.
    check_carry_on_overflow: assert property (
        @($global_clock) (({1'b0, A} + {1'b0, B}) >= 5'd16) |-> (CO == 1'b1)
    );

    // Carry-out must be low when the 4-bit sum does not overflow.
    check_carry_without_overflow: assert property (
        @($global_clock) (({1'b0, A} + {1'b0, B}) < 5'd16) |-> (CO == 1'b0)
    );

    // Zero plus zero must produce zero with no carry.
    check_zero_plus_zero: assert property (
        @($global_clock) ((A == 4'd0) && (B == 4'd0)) |-> ((C == 4'd0) && (CO == 1'b0))
    );

    // Adding zero on B must pass A through with no carry.
    check_add_zero_b: assert property (
        @($global_clock) (B == 4'd0) |-> ((C == A) && (CO == 1'b0))
    );

    // Adding zero on A must pass B through with no carry.
    check_add_zero_a: assert property (
        @($global_clock) (A == 4'd0) |-> ((C == B) && (CO == 1'b0))
    );

    // The maximum input pair must produce 0xE with carry-out set.
    check_max_plus_max: assert property (
        @($global_clock) ((A == 4'd15) && (B == 4'd15)) |-> ((C == 4'd14) && (CO == 1'b1))
    );

endmodule