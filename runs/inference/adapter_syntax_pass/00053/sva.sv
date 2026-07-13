module adder_4bit_carry_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // The 5-bit output must equal the 4-bit addition plus carry-in.
    check_full_add_result: assert property (
        @($global_clock)
        {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0000, cin})
    );

    // The least-significant sum bit must match the LSB full-adder equation.
    check_lsb_sum_equation: assert property (
        @($global_clock)
        sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Zero inputs must produce a zero result.
    check_zero_inputs_zero_output: assert property (
        @($global_clock)
        ((a == 4'h0) && (b == 4'h0) && (cin == 1'b0)) |-> ((sum == 4'h0) && (cout == 1'b0))
    );

    // Adding zero with no carry-in must pass a through unchanged.
    check_pass_a_when_b_zero_and_no_carry: assert property (
        @($global_clock)
        ((b == 4'h0) && (cin == 1'b0)) |-> ((sum == a) && (cout == 1'b0))
    );

    // Adding zero with no carry-in must pass b through unchanged.
    check_pass_b_when_a_zero_and_no_carry: assert property (
        @($global_clock)
        ((a == 4'h0) && (cin == 1'b0)) |-> ((sum == b) && (cout == 1'b0))
    );

    // All-ones inputs with carry-in must produce the maximum 5-bit result.
    check_all_ones_maximum_result: assert property (
        @($global_clock)
        ((a == 4'hF) && (b == 4'hF) && (cin == 1'b1)) |-> ((sum == 4'hF) && (cout == 1'b1))
    );

endmodule