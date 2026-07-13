module sparc_ffu_part_add32_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        cin,
    input logic        add32,
    input logic [31:0] z
);

    // Lower 16 bits always add a, b, and cin.
    check_lower_half_sum: assert property (
        @(posedge clk)
        z[15:0] == (a[15:0] + b[15:0] + cin)
    );

    // In split mode, both halves add independently with the same cin.
    check_split_mode_full_output: assert property (
        @(posedge clk)
        !add32 |-> (z == {(a[31:16] + b[31:16] + cin), (a[15:0] + b[15:0] + cin)})
    );

    // In 32-bit mode, the output matches a full 32-bit add.
    check_add32_mode_full_sum: assert property (
        @(posedge clk)
        add32 |-> (z == (a + b + cin))
    );

    // In 32-bit mode, a carry from bit 15 increments the upper half.
    check_add32_upper_with_lower_carry: assert property (
        @(posedge clk)
        add32 && (({1'b0, a[15:0]} + {1'b0, b[15:0]} + cin) >= 17'h10000)
        |-> (z[31:16] == (a[31:16] + b[31:16] + 16'h0001))
    );

    // In 32-bit mode, no carry from bit 15 leaves the upper half unincremented.
    check_add32_upper_without_lower_carry: assert property (
        @(posedge clk)
        add32 && (({1'b0, a[15:0]} + {1'b0, b[15:0]} + cin) < 17'h10000)
        |-> (z[31:16] == (a[31:16] + b[31:16]))
    );

    // In split mode, lower-half carry does not affect the upper half.
    check_split_mode_ignores_lower_carry: assert property (
        @(posedge clk)
        !add32 && (({1'b0, a[15:0]} + {1'b0, b[15:0]} + cin) >= 17'h10000)
        |-> (z[31:16] == (a[31:16] + b[31:16] + cin))
    );

endmodule