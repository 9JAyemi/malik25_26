module four_bit_adder_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    // Sum and carry must match the 5-bit addition of a, b, and cin.
    check_full_add_result: assert property (
        @($global_clock) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // Carry-out must assert when the 5-bit sum exceeds 4 bits.
    check_cout_threshold: assert property (
        @($global_clock) cout == (({1'b0, a} + {1'b0, b} + cin) > 5'd15)
    );

    // Carry-out must deassert when the 5-bit sum is 4 bits or less.
    check_no_cout_threshold: assert property (
        @($global_clock) !cout == (({1'b0, a} + {1'b0, b} + cin) <= 5'd15)
    );

    // Adding zero on b with no carry-in must pass a through unchanged.
    check_add_zero_b: assert property (
        @($global_clock) (b == 4'd0 && cin == 1'b0) |-> (sum == a && cout == 1'b0)
    );

    // Adding zero on a with no carry-in must pass b through unchanged.
    check_add_zero_a: assert property (
        @($global_clock) (a == 4'd0 && cin == 1'b0) |-> (sum == b && cout == 1'b0)
    );

    // With a and b at zero, carry-in must increment the sum to one.
    check_cin_only: assert property (
        @($global_clock) (a == 4'd0 && b == 4'd0) |-> (sum == 4'd1 && cout == 1'b0)
    );

    // With a and b at 15, carry-in must produce the maximum 5-bit result.
    check_max_plus_cin: assert property (
        @($global_clock) (a == 4'd15 && b == 4'd15) |-> (sum == 4'd15 && cout == 1'b1)
    );

    // Carry-out must never assert for zero inputs.
    check_cout_zero_inputs: assert property (
        @($global_clock) (a == 4'd0 && b == 4'd0 && cin == 1'b0) |-> (cout == 1'b0)
    );

endmodule