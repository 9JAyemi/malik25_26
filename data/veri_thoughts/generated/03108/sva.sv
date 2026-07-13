module dual_d_flip_flop_sva (
    input logic clk,
    input logic reset,
    input logic d_in,
    input logic d_out_1,
    input logic d_out_2
);

    // Active-low reset clears d_out_1.
    check_reset_clears_dout1: assert property (
        @(posedge clk) !reset |-> (d_out_1 == 1'b0)
    );

    // Active-low reset clears d_out_2.
    check_reset_clears_dout2: assert property (
        @(posedge clk) !reset |-> (d_out_2 == 1'b0)
    );

    // The first clock after reset release still sees cleared outputs.
    check_outputs_zero_on_reset_release: assert property (
        @(posedge clk) disable iff (!reset) $past(!reset) |-> ((d_out_1 == 1'b0) && (d_out_2 == 1'b0))
    );

    // d_out_1 captures d_in on the next active clock.
    check_dout1_captures_din: assert property (
        @(posedge clk) disable iff (!reset) reset |=> (d_out_1 == $past(d_in))
    );

    // d_out_2 captures the previous d_out_1 ^ d_in on the next active clock.
    check_dout2_captures_xor: assert property (
        @(posedge clk) disable iff (!reset) reset |=> (d_out_2 == ($past(d_out_1) ^ $past(d_in)))
    );

endmodule