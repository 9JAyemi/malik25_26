module sixteen_bit_adder_sva (
    input logic        clk,
    input logic        reset,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic        carry_in,
    input logic [15:0] sum,
    input logic        carry_out
);

    // Full output matches 16-bit addition with carry-in.
    check_full_addition: assert property (
        @(posedge clk) disable iff (reset)
        {carry_out, sum} == ({1'b0, a} + {1'b0, b} + carry_in)
    );

    // carry_out is high only when the full addition overflows 16 bits.
    check_carry_out_matches_overflow: assert property (
        @(posedge clk) disable iff (reset)
        carry_out == (({1'b0, a} + {1'b0, b} + carry_in) >= 17'h10000)
    );

    // Adding zero on b with no carry-in leaves a unchanged.
    check_zero_b_identity: assert property (
        @(posedge clk) disable iff (reset)
        (b == 16'h0000 && carry_in == 1'b0) |-> (sum == a && carry_out == 1'b0)
    );

    // Adding zero on a with no carry-in leaves b unchanged.
    check_zero_a_identity: assert property (
        @(posedge clk) disable iff (reset)
        (a == 16'h0000 && carry_in == 1'b0) |-> (sum == b && carry_out == 1'b0)
    );

    // The least-significant sum bit follows 1-bit full-adder behavior.
    check_lsb_full_adder_relation: assert property (
        @(posedge clk) disable iff (reset)
        sum[0] == (a[0] ^ b[0] ^ carry_in)
    );

    // If the low byte does not overflow, the upper byte adds without carry-in.
    check_upper_byte_without_low_carry: assert property (
        @(posedge clk) disable iff (reset)
        (({1'b0, a[7:0]} + {1'b0, b[7:0]} + carry_in) < 9'h100) |->
        ({carry_out, sum[15:8]} == ({1'b0, a[15:8]} + {1'b0, b[15:8]}))
    );

    // If the low byte overflows, the upper byte adds with a propagated carry.
    check_upper_byte_with_low_carry: assert property (
        @(posedge clk) disable iff (reset)
        (({1'b0, a[7:0]} + {1'b0, b[7:0]} + carry_in) >= 9'h100) |->
        ({carry_out, sum[15:8]} == ({1'b0, a[15:8]} + {1'b0, b[15:8]} + 1'b1))
    );

endmodule