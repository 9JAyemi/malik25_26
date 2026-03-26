module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    // The 5-bit output must equal a + b + cin.
    check_total_addition: assert property (
        @(posedge clk) disable iff (1'b0)
        {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0000, cin})
    );

    // Sum bit 0 must match the first full-adder stage.
    check_sum_bit0: assert property (
        @(posedge clk) disable iff (1'b0)
        sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Sum bit 1 must use the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) disable iff (1'b0)
        sum[1] == (
            a[1] ^ b[1] ^
            ((a[0] & b[0]) | ((a[0] ^ b[0]) & cin))
        )
    );

    // Sum bit 2 must use the carry from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) disable iff (1'b0)
        sum[2] == (
            a[2] ^ b[2] ^
            (
                (a[1] & b[1]) |
                ((a[1] ^ b[1]) & (
                    (a[0] & b[0]) |
                    ((a[0] ^ b[0]) & cin)
                ))
            )
        )
    );

    // Sum bit 3 must use the carry from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) disable iff (1'b0)
        sum[3] == (
            a[3] ^ b[3] ^
            (
                (a[2] & b[2]) |
                ((a[2] ^ b[2]) & (
                    (a[1] & b[1]) |
                    ((a[1] ^ b[1]) & (
                        (a[0] & b[0]) |
                        ((a[0] ^ b[0]) & cin)
                    ))
                ))
            )
        )
    );

    // Cout must be the carry out of the MSB full-adder stage.
    check_cout_bit3: assert property (
        @(posedge clk) disable iff (1'b0)
        cout == (
            (a[3] & b[3]) |
            ((a[3] ^ b[3]) & (
                (a[2] & b[2]) |
                ((a[2] ^ b[2]) & (
                    (a[1] & b[1]) |
                    ((a[1] ^ b[1]) & (
                        (a[0] & b[0]) |
                        ((a[0] ^ b[0]) & cin)
                    ))
                ))
            ))
        )
    );

    // Adding zero with cin low must pass a through unchanged.
    check_add_zero_to_a: assert property (
        @(posedge clk) disable iff (1'b0)
        (b == 4'b0000 && cin == 1'b0) |-> ({cout, sum} == {1'b0, a})
    );

    // Adding zero with cin low must pass b through unchanged.
    check_add_zero_to_b: assert property (
        @(posedge clk) disable iff (1'b0)
        (a == 4'b0000 && cin == 1'b0) |-> ({cout, sum} == {1'b0, b})
    );

endmodule