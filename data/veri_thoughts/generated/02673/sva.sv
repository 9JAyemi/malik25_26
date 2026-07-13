module multiply_by_3_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [5:0] out
);
    // out equals zero-extended (a<<1) plus a (matches RTL's two blocking assignments)
    check_function_exact: assert property (
        @(posedge clk) out == ({2'b00, (a << 1)} + a)
    );

    // MSB of out is always 0 (out <= 29)
    check_out_msb_zero: assert property (
        @(posedge clk) out[5] == 1'b0
    );

    // Output never less than input
    check_out_ge_a: assert property (
        @(posedge clk) out >= a
    );

    // Output is bounded by 29
    check_out_le_29: assert property (
        @(posedge clk) out <= 6'd29
    );

    // For a == 0, out == 0
    check_out_zero_when_a_zero: assert property (
        @(posedge clk) (a == 4'd0) |-> (out == 6'd0)
    );

    // For a == 1, out == 3
    check_out_three_when_a_one: assert property (
        @(posedge clk) (a == 4'd1) |-> (out == 6'd3)
    );

    // For a == 8, out == 8 (due to 4-bit shift wrap in first step)
    check_out_eight_when_a_eight: assert property (
        @(posedge clk) (a == 4'd8) |-> (out == 6'd8)
    );

    // For a == 15, out == 29
    check_out_29_when_a_15: assert property (
        @(posedge clk) (a == 4'd15) |-> (out == 6'd29)
    );

    // LSB of out equals LSB of a (3 is odd)
    check_lsb_matches_a: assert property (
        @(posedge clk) out[0] == a[0]
    );

    // When a[3]==0 (a<8), out equals 3*a without wrap
    check_low_range_exact: assert property (
        @(posedge clk) (!a[3]) |-> (out == (({2'b00, a} << 1) + {2'b00, a}))
    );
endmodule