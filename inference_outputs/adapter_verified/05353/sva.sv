module reverse_bit_order_sva (
    input logic [99:0] in,
    input logic        clk,
    input logic [99:0] out
);

// out[0] captures the previous cycle's MSB of in.
    check_out0_captures_prev_msb: assert property (
        @(posedge clk) 1'b1 |=> (out[0] == $past(in[99]))
    );

// out[99] captures the previous cycle's LSB of in.
    check_out99_captures_prev_lsb: assert property (
        @(posedge clk) 1'b1 |=> (out[99] == $past(in[0]))
    );

// out[1:98] shifts left by one bit from the previous cycle's in[98:1].
    check_out_middle_captures_prev_middle: assert property (
        @(posedge clk) 1'b1 |=> (out[98:1] == $past(in[98:1]))
    );

// out equals the previous cycle's in with the MSB and LSB swapped.
    check_out_is_prev_in_with_swapped_ends: assert property (
        @(posedge clk) 1'b1 |=> (out == {$past(in[0]), $past(in[98:1]), $past(in[99])})
    );

endmodule
