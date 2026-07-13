module adder_4bit_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    // No RTL clock or reset; sample this combinational DUT on the global clock.

    // Full result must match 4-bit addition with carry-in.
    check_full_add_result: assert property (
        @($global_clock)
        {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0000, cin})
    );

    // Carry-out must indicate arithmetic overflow beyond 4 bits.
    check_carry_out_matches_overflow: assert property (
        @($global_clock)
        cout == (({1'b0, a} + {1'b0, b} + {4'b0000, cin}) > 5'd15)
    );

    // The least-significant sum bit must be the XOR of the input bits.
    check_lsb_sum_bit: assert property (
        @($global_clock)
        sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // All-zero inputs must produce an all-zero result.
    check_zero_inputs: assert property (
        @($global_clock)
        (a == 4'b0000 && b == 4'b0000 && cin == 1'b0) |-> ({cout, sum} == 5'b00000)
    );

    // Adding zero with no carry-in must pass a through.
    check_a_passthrough: assert property (
        @($global_clock)
        (b == 4'b0000 && cin == 1'b0) |-> (sum == a && cout == 1'b0)
    );

    // Adding zero with no carry-in must pass b through.
    check_b_passthrough: assert property (
        @($global_clock)
        (a == 4'b0000 && cin == 1'b0) |-> (sum == b && cout == 1'b0)
    );

endmodule