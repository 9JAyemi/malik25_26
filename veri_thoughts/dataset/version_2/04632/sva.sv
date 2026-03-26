module four_bit_adder_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // Combined outputs must equal the 5-bit sum of a, b, and cin.
    check_full_add_result: assert property (
        @($global_clock)
        {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0, cin})
    );

    // sum must match the low 4 bits of the arithmetic result.
    check_sum_matches_low_bits: assert property (
        @($global_clock)
        {1'b0, sum} == (({1'b0, a} + {1'b0, b} + {4'b0, cin}) & 5'h0F)
    );

    // cout must assert exactly when the addition overflows 4 bits.
    check_cout_matches_overflow: assert property (
        @($global_clock)
        cout == (({1'b0, a} + {1'b0, b} + {4'b0, cin}) > 5'd15)
    );

    // All-zero inputs must produce a zero result.
    check_zero_inputs_zero_outputs: assert property (
        @($global_clock)
        (a == 4'b0000 && b == 4'b0000 && cin == 1'b0) |-> ({cout, sum} == 5'b00000)
    );

    // Maximum inputs must produce the maximum 5-bit result.
    check_max_inputs_max_output: assert property (
        @($global_clock)
        (a == 4'b1111 && b == 4'b1111 && cin == 1'b1) |-> ({cout, sum} == 5'b11111)
    );

endmodule