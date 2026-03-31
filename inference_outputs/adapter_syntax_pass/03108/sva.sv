module dual_d_flip_flop_sva (
    input logic clk,
    input logic reset,
    input logic d_in,
    input logic d_out_1,
    input logic d_out_2
);

    // d_out_1 is the D input sampled on the previous rising edge.
    check_d_out_1_captures_d_in: assert property (
        @(posedge clk) disable iff (!reset)
        1'b1 |=> (d_out_1 == $past(d_in))
    );

    // d_out_2 is the XOR of the previous d_out_1 and d_in.
    check_d_out_2_captures_toggle: assert property (
        @(posedge clk) disable iff (!reset)
        1'b1 |=> (d_out_2 == ($past(d_out_1) ^ $past(d_in)))
    );

    // d_out_2 is the previous d_out_1 value.
    check_d_out_2_tracks_previous_d_out_1: assert property (
        @(posedge clk) disable iff (!reset)
        1'b1 |=> (d_out_2 == $past(d_out_1))
    );

    // A low reset clears both outputs by the next rising edge.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        !reset |=> ((d_out_1 == 1'b0) && (d_out_2 == 1'b0))
    );

endmodule