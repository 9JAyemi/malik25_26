module adder4_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // The 5-bit output must equal a + b + cin.
    check_total_sum: assert property (
        @($global_clock) {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0000, cin})
    );

    // Bit 0 sum must match the first full-adder XOR.
    check_bit0_sum: assert property (
        @($global_clock) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Bit 1 sum must use the carry from bit 0.
    check_bit1_sum: assert property (
        @($global_clock) sum[1] == (a[1] ^ b[1] ^ ((a[0] & b[0]) | (cin & a[0]) | (cin & b[0])))
    );

    // Bit 2 sum must use the carry from bit 1.
    check_bit2_sum: assert property (
        @($global_clock) sum[2] == (a[2] ^ b[2] ^ (
            (a[1] & b[1]) |
            (((a[0] & b[0]) | (cin & a[0]) | (cin & b[0]))) & (a[1] | b[1])
        ))
    );

    // Bit 3 sum must use the carry from bit 2.
    check_bit3_sum: assert property (
        @($global_clock) sum[3] == (a[3] ^ b[3] ^ (
            (a[2] & b[2]) |
            (
                ((a[1] & b[1]) |
                 (((a[0] & b[0]) | (cin & a[0]) | (cin & b[0]))) & (a[1] | b[1]))
                ) & (a[2] | b[2])
            )
        ))
    );

    // Carry-out must match the final full-adder carry.
    check_cout: assert property (
        @($global_clock) cout == (
            (a[3] & b[3]) |
            (
                ((a[2] & b[2]) |
                 (
                     ((a[1] & b[1]) |
                      (((a[0] & b[0]) | (cin & a[0]) | (cin & b[0]))) & (a[1] | b[1])
                     ) & (a[2] | b[2])
                 )
                ) & (a[3] | b[3])
            )
        )
    );

endmodule