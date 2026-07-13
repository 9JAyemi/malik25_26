module dual_d_flip_flop_sva (
    input logic clk,
    input logic reset,
    input logic d_in,
    input logic d_out_1,
    input logic d_out_2
);

// d_out_1 is the registered input on the next clock.
    check_d_out_1_captures_d_in: assert property (
        @(posedge clk) disable iff (!reset) 1'b1 |=> (d_out_1 == $past(d_in))
    );

// d_out_2 is the registered toggle of the previous d_out_1 and current d_in.
    check_d_out_2_captures_toggle: assert property (
        @(posedge clk) disable iff (!reset) 1'b1 |=> (d_out_2 == ($past(d_out_1) ^ d_in))
    );

// A low reset keeps both outputs low on the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk) !reset |=> (d_out_1 == 1'b0) && (d_out_2 == 1'b0)
    );

// A high d_out_2 indicates the previous d_out_1 and current d_in differ.
    check_d_out_2_high_means_toggle: assert property (
        @(posedge clk) disable iff (!reset) 1'b1 |=> (d_out_2 == 1'b1) |-> ($past(d_out_1) != d_in)
    );

// A low d_out_2 indicates the previous d_out_1 and current d_in are equal.
    check_d_out_2_low_means_no_toggle: assert property (
        @(posedge clk) disable iff (!reset) 1'b1 |=> (d_out_2 == 1'b0) |-> ($past(d_out_1) == d_in)
    );

endmodule
