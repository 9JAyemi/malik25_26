module adder_4bit_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] s,
    input logic       cout
);

    // Combined outputs must equal the 5-bit sum of the inputs.
    check_full_sum: assert property (
        @($global_clock)
        {cout, s} == ({1'b0, a} + {1'b0, b} + {4'b0000, cin})
    );

    // s must be the low 4 bits of the arithmetic result.
    check_sum_bits: assert property (
        @($global_clock)
        s == (({1'b0, a} + {1'b0, b} + {4'b0000, cin}))[3:0]
    );

    // cout must be the carry-out bit of the arithmetic result.
    check_carry_out: assert property (
        @($global_clock)
        cout == (({1'b0, a} + {1'b0, b} + {4'b0000, cin}))[4]
    );

    // With b and cin low, the adder must pass a through unchanged.
    check_pass_a_when_b_and_cin_zero: assert property (
        @($global_clock)
        ((b == 4'h0) && (cin == 1'b0)) |-> ((s == a) && (cout == 1'b0))
    );

    // With a and cin low, the adder must pass b through unchanged.
    check_pass_b_when_a_and_cin_zero: assert property (
        @($global_clock)
        ((a == 4'h0) && (cin == 1'b0)) |-> ((s == b) && (cout == 1'b0))
    );

    // With a and b low, the adder must produce cin on s and no carry.
    check_cin_only_when_a_and_b_zero: assert property (
        @($global_clock)
        ((a == 4'h0) && (b == 4'h0)) |-> ((s == {3'b000, cin}) && (cout == 1'b0))
    );

    // With a and b at 4'hF, the adder must produce 4'h0 and assert carry.
    check_max_plus_max: assert property (
        @($global_clock)
        ((a == 4'hF) && (b == 4'hF)) |-> ((s == 4'h0) && (cout == 1'b1))
    );

endmodule