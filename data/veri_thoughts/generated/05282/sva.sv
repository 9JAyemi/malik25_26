module cond_sum_sva (
    input logic [3:0] X,
    input logic [3:0] Y,
    input logic Cin,
    input logic [3:0] Sum,
    input logic C_out
);

    // Full output matches 4-bit addition with carry-in.
    check_full_add_result: assert property (
        @($global_clock)
        {C_out, Sum} == ({1'b0, X} + {1'b0, Y} + Cin)
    );

    // Sum[0] is the bit-0 full-adder sum.
    check_sum_bit0: assert property (
        @($global_clock)
        Sum[0] == (X[0] ^ Y[0] ^ Cin)
    );

    // Sum[1] uses the carry from bit 0.
    check_sum_bit1: assert property (
        @($global_clock)
        Sum[1] == (X[1] ^ Y[1] ^ ((X[0] & Y[0]) | (Cin & (X[0] ^ Y[0]))))
    );

    // Sum[2] uses the carry from the lower two bits.
    check_sum_bit2: assert property (
        @($global_clock)
        Sum[2] == (X[2] ^ Y[2] ^ (({1'b0, X[1:0]} + {1'b0, Y[1:0]} + Cin) > 3'd3))
    );

    // Sum[3] uses the carry from the lower three bits.
    check_sum_bit3: assert property (
        @($global_clock)
        Sum[3] == (X[3] ^ Y[3] ^ (({1'b0, X[2:0]} + {1'b0, Y[2:0]} + Cin) > 4'd7))
    );

    // C_out is the carry out of the 4-bit addition.
    check_carry_out: assert property (
        @($global_clock)
        C_out == (({1'b0, X} + {1'b0, Y} + Cin) > 5'd15)
    );

    // Cin low selects plain X + Y.
    check_no_carry_in_path: assert property (
        @($global_clock)
        !Cin |-> ({C_out, Sum} == ({1'b0, X} + {1'b0, Y}))
    );

    // Cin high selects X + Y + 1.
    check_carry_in_path: assert property (
        @($global_clock)
        Cin |-> ({C_out, Sum} == ({1'b0, X} + {1'b0, Y} + 5'd1))
    );

    // Stable inputs keep outputs stable.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock)
        (!$initstate && $stable({X, Y, Cin})) |-> $stable({C_out, Sum})
    );

    // Sum[1:0] depends only on X[1:0], Y[1:0], and Cin.
    check_low_two_bits_local: assert property (
        @($global_clock)
        (!$initstate && $stable({X[1:0], Y[1:0], Cin})) |-> $stable(Sum[1:0])
    );

    // Sum[2:0] depends only on X[2:0], Y[2:0], and Cin.
    check_low_three_bits_local: assert property (
        @($global_clock)
        (!$initstate && $stable({X[2:0], Y[2:0], Cin})) |-> $stable(Sum[2:0])
    );

endmodule