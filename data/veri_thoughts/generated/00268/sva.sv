module add_sub_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic mode,
    input logic [3:0] O,
    input logic COUT
);

    // Addition mode must drive the concatenated result from A + B.
    check_add_result: assert property (
        @($global_clock) (mode == 1'b0) |-> ({COUT, O} == (A + B))
    );

    // Subtraction mode must drive the concatenated result from A - B.
    check_sub_result: assert property (
        @($global_clock) (mode == 1'b1) |-> ({COUT, O} == (A - B))
    );

    // Adding zero on B must pass A through unchanged.
    check_add_zero_b_identity: assert property (
        @($global_clock) ((mode == 1'b0) && (B == 4'b0000)) |-> ({COUT, O} == A)
    );

    // Adding zero on A must pass B through unchanged.
    check_add_zero_a_identity: assert property (
        @($global_clock) ((mode == 1'b0) && (A == 4'b0000)) |-> ({COUT, O} == B)
    );

    // Subtracting zero must pass A through unchanged.
    check_sub_zero_b_identity: assert property (
        @($global_clock) ((mode == 1'b1) && (B == 4'b0000)) |-> ({COUT, O} == A)
    );

    // Subtracting equal operands must produce zero.
    check_sub_equal_operands_zero: assert property (
        @($global_clock) ((mode == 1'b1) && (A == B)) |-> ({COUT, O} == 5'b00000)
    );

endmodule