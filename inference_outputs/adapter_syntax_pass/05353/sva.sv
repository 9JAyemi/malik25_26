module reverse_bit_order_sva (
    input logic [99:0] in,
    input logic        clk,
    input logic [99:0] out
);

    // out[0] is the previous cycle's in[0].
    check_out0_captures_in0: assert property (
        @(posedge clk) 1'b1 |=> (out[0] == $past(in[0]))
    );

    // out[1] is the previous cycle's in[1].
    check_out1_captures_in1: assert property (
        @(posedge clk) 1'b1 |=> (out[1] == $past(in[1]))
    );

    // out[99] is the previous cycle's in[98].
    check_out99_captures_in98: assert property (
        @(posedge clk) 1'b1 |=> (out[99] == $past(in[98]))
    );

    // out[98] is the previous cycle's in[99].
    check_out98_captures_in99: assert property (
        @(posedge clk) 1'b1 |=> (out[98] == $past(in[99]))
    );

    // out[99:1] is the previous cycle's in[98:0].
    check_out_upper_captures_in_lower: assert property (
        @(posedge clk) 1'b1 |=> (out[99:1] == $past(in[98:0]))
    );

    // out[99:0] is the previous cycle's in[99:0].
    check_out_captures_in: assert property (
        @(posedge clk) 1'b1 |=> (out == $past(in))
    );

endmodule