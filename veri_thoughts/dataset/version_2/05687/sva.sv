module carry_lookahead_adder_sva (
    input logic        clk,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [31:0] sum
);

    // Sum matches the RTL carry equations and concatenation add.
    check_sum_matches_rtl: assert property (
        @(posedge clk)
        sum == (
            {28'b0,
             ((a[3] & b[3]) |
              ((a[3] ^ b[3]) & (a[2] & b[2])) |
              ((a[3] ^ b[3]) & (a[2] ^ b[2]) & (a[1] & b[1])) |
              ((a[3] ^ b[3]) & (a[2] ^ b[2]) & (a[1] ^ b[1]) & (a[0] & b[0]))),
             ((a[2] & b[2]) |
              ((a[2] ^ b[2]) & (a[1] & b[1])) |
              ((a[2] ^ b[2]) & (a[1] ^ b[1]) & (a[0] & b[0]))),
             ((a[1] & b[1]) |
              ((a[1] ^ b[1]) & (a[0] & b[0]))),
             (a[0] & b[0])}
            + {a, b}
        )
    );

    // Low 16 bits are b plus the four carry bits.
    check_low_half_matches_rtl: assert property (
        @(posedge clk)
        sum[15:0] == (
            b + {12'b0,
                 ((a[3] & b[3]) |
                  ((a[3] ^ b[3]) & (a[2] & b[2])) |
                  ((a[3] ^ b[3]) & (a[2] ^ b[2]) & (a[1] & b[1])) |
                  ((a[3] ^ b[3]) & (a[2] ^ b[2]) & (a[1] ^ b[1]) & (a[0] & b[0]))),
                 ((a[2] & b[2]) |
                  ((a[2] ^ b[2]) & (a[1] & b[1])) |
                  ((a[2] ^ b[2]) & (a[1] ^ b[1]) & (a[0] & b[0]))),
                 ((a[1] & b[1]) |
                  ((a[1] ^ b[1]) & (a[0] & b[0]))),
                 (a[0] & b[0])}
        )
    );

    // Sum bit 0 follows b[0] plus c[0].
    check_sum_bit0_behavior: assert property (
        @(posedge clk)
        sum[0] == (b[0] & ~a[0])
    );

    // No low-nibble generate means the output is just {a,b}.
    check_no_generate_passthrough: assert property (
        @(posedge clk)
        ((a[3:0] & b[3:0]) == 4'b0000) |-> (sum == {a, b})
    );

    // All low-nibble generates force the adder to add 15.
    check_all_generate_adds_fifteen: assert property (
        @(posedge clk)
        ((a[3:0] & b[3:0]) == 4'b1111) |-> (sum == ({a, b} + 32'd15))
    );

    // With bits [3:1] clear, only c[0] can contribute.
    check_only_bit0_region_can_add: assert property (
        @(posedge clk)
        ((a[3:1] == 3'b000) && (b[3:1] == 3'b000)) |-> (sum == ({a, b} + {31'b0, (a[0] & b[0])}))
    );

    // With bits [3:2] clear and no bit0 generate, only c[1] can contribute.
    check_only_bit1_region_can_add: assert property (
        @(posedge clk)
        ((a[3:2] == 2'b00) && (b[3:2] == 2'b00) && ((a[0] & b[0]) == 1'b0)) |-> (sum == ({a, b} + {30'b0, (a[1] & b[1]), 1'b0}))
    );

endmodule