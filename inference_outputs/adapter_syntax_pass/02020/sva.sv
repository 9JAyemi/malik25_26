module four_bit_adder_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    // Sum and carry match the 5-bit addition of a, b, and cin.
    check_full_add_result: assert property (
        @($global_clock)
        {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0000, cin})
    );

    // Carry is asserted exactly when the 4-bit result overflows 15.
    check_carry_matches_overflow: assert property (
        @($global_clock)
        cout == (({1'b0, a} + {1'b0, b} + {4'b0000, cin}) > 5'd15)
    );

    // Zero inputs produce a zero result.
    check_zero_inputs_zero_result: assert property (
        @($global_clock)
        ((a == 4'd0) && (b == 4'd0) && (cin == 1'b0)) |-> ((sum == 4'd0) && (cout == 1'b0))
    );

    // Adding zero with no carry-in passes a through unchanged.
    check_a_passthrough_when_b_zero: assert property (
        @($global_clock)
        ((b == 4'd0) && (cin == 1'b0)) |-> ((sum == a) && (cout == 1'b0))
    );

    // Adding zero with no carry-in passes b through unchanged.
    check_b_passthrough_when_a_zero: assert property (
        @($global_clock)
        ((a == 4'd0) && (cin == 1'b0)) |-> ((sum == b) && (cout == 1'b0))
    );

    // Maximum inputs produce the maximum 5-bit result.
    check_max_inputs_max_result: assert property (
        @($global_clock)
        ((a == 4'hF) && (b == 4'hF) && (cin == 1'b1)) |-> ((sum == 4'hF) && (cout == 1'b1))
    );

endmodule