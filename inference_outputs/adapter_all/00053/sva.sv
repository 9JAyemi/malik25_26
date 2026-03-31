module adder_4bit_carry_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // sum and cout must match the 5-bit addition of a, b, and cin.
    check_full_add_result: assert property (
        @($global_clock) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // sum must match the low 4 bits of the addition result.
    check_sum_low_bits: assert property (
        @($global_clock) sum == (({1'b0, a} + {1'b0, b} + cin)[3:0])
    );

    // cout must match the carry-out bit of the addition result.
    check_cout_carry: assert property (
        @($global_clock) cout == (({1'b0, a} + {1'b0, b} + cin)[4])
    );

    // Adding zero with no carry-in must pass a through unchanged.
    check_add_zero_a: assert property (
        @($global_clock) (b == 4'b0000 && cin == 1'b0) |-> (sum == a && cout == 1'b0)
    );

    // Adding zero with no carry-in must pass b through unchanged.
    check_add_zero_b: assert property (
        @($global_clock) (a == 4'b0000 && cin == 1'b0) |-> (sum == b && cout == 1'b0)
    );

    // With a and b at zero, carry-in must increment the result by one.
    check_cin_only: assert property (
        @($global_clock) (a == 4'b0000 && b == 4'b0000) |-> (sum == 4'b0001 && cout == 1'b0)
    );

    // All-zero inputs must produce an all-zero result.
    check_zero_inputs: assert property (
        @($global_clock) (a == 4'b0000 && b == 4'b0000 && cin == 1'b0) |-> (sum == 4'b0000 && cout == 1'b0)
    );

    // All-ones inputs with carry-in must produce the maximum 5-bit result.
    check_max_inputs: assert property (
        @($global_clock) (a == 4'b1111 && b == 4'b1111 && cin == 1'b1) |-> (sum == 4'b1111 && cout == 1'b1)
    );

endmodule