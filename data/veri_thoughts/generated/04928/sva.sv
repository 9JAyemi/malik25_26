module adder4_sva (
    input logic        clk,
    input logic [3:0]  a,
    input logic [3:0]  b,
    input logic        cin,
    input logic [3:0]  sum,
    input logic        cout
);

    // Full 5-bit result matches a + b + cin.
    check_full_result: assert property (
        @(posedge clk)
        {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0000, cin})
    );

    // Bit 0 sum is the XOR of a[0], b[0], and cin.
    check_sum_bit0: assert property (
        @(posedge clk)
        sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Bit 1 sum uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk)
        sum[1] == (a[1] ^ b[1] ^ ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin)))
    );

    // Bit 2 sum uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk)
        sum[2] == (a[2] ^ b[2] ^ (
            (a[1] & b[1]) |
            (a[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin))) |
            (b[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin)))
        ))
    );

    // Bit 3 sum uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk)
        sum[3] == (a[3] ^ b[3] ^ (
            (a[2] & b[2]) |
            (a[2] & (
                (a[1] & b[1]) |
                (a[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin))) |
                (b[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin)))
            )) |
            (b[2] & (
                (a[1] & b[1]) |
                (a[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin))) |
                (b[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin)))
            ))
        ))
    );

    // cout is the carry out generated from the top bit.
    check_cout_formula: assert property (
        @(posedge clk)
        cout == (
            (a[3] & b[3]) |
            (a[3] & (
                (a[2] & b[2]) |
                (a[2] & (
                    (a[1] & b[1]) |
                    (a[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin))) |
                    (b[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin)))
                )) |
                (b[2] & (
                    (a[1] & b[1]) |
                    (a[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin))) |
                    (b[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin)))
                ))
            )) |
            (b[3] & (
                (a[2] & b[2]) |
                (a[2] & (
                    (a[1] & b[1]) |
                    (a[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin))) |
                    (b[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin)))
                )) |
                (b[2] & (
                    (a[1] & b[1]) |
                    (a[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin))) |
                    (b[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin)))
                ))
            ))
        )
    );

endmodule