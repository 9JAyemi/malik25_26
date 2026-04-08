module four_bit_adder_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    // Carry and sum together must match the 5-bit addition result.
    check_full_addition: assert property (
        @($global_clock) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // Sum must be the low four bits of the addition result.
    check_sum_low_bits: assert property (
        @($global_clock) {1'b0, sum} == (({1'b0, a} + {1'b0, b} + cin) & 5'h0f)
    );

    // Carry-out must assert only when the addition exceeds 4 bits.
    check_carry_out: assert property (
        @($global_clock) cout == (({1'b0, a} + {1'b0, b} + cin) > 5'd15)
    );

    // All-zero inputs must produce zero outputs.
    check_zero_case: assert property (
        @($global_clock) ((a == 4'd0) && (b == 4'd0) && (cin == 1'b0)) |-> ((sum == 4'd0) && (cout == 1'b0))
    );

    // Adding zero with no carry-in must pass through a.
    check_pass_through_a: assert property (
        @($global_clock) ((b == 4'd0) && (cin == 1'b0)) |-> ((sum == a) && (cout == 1'b0))
    );

    // Adding zero with no carry-in must pass through b.
    check_pass_through_b: assert property (
        @($global_clock) ((a == 4'd0) && (cin == 1'b0)) |-> ((sum == b) && (cout == 1'b0))
    );

    // Maximum inputs must produce 0xF with carry-out asserted.
    check_max_input_case: assert property (
        @($global_clock) ((a == 4'hf) && (b == 4'hf) && (cin == 1'b1)) |-> ((sum == 4'hf) && (cout == 1'b1))
    );

endmodule