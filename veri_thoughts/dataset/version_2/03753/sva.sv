module latch_module_sva (
    input logic clk,
    input logic din,
    input logic reset_n,
    input logic dout
);

    // Reset clears the output on any sampled clock while reset is active.
    check_reset_forces_dout_low: assert property (
        @(posedge clk) !reset_n |-> (dout == 1'b0)
    );

    // A sampled active reset keeps the output low on the next clock.
    check_reset_keeps_dout_low_next_cycle: assert property (
        @(posedge clk) !reset_n |=> (dout == 1'b0)
    );

    // A sampled active reset keeps the output low for one additional clock.
    check_reset_keeps_dout_low_two_cycles_later: assert property (
        @(posedge clk) !reset_n |=> ##1 (dout == 1'b0)
    );

    // A high output requires reset to have been inactive on the prior sampled clock.
    check_high_dout_requires_reset_inactive_prev_cycle: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!$initstate && (dout == 1'b1)) |-> $past(reset_n)
    );

    // A high output requires reset to have been inactive two sampled clocks earlier.
    check_high_dout_requires_reset_inactive_two_cycles_back: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!$initstate && !$past($initstate) && (dout == 1'b1)) |-> $past(reset_n, 2)
    );

    // A high output can only come from a high input sampled two clocks earlier.
    check_high_dout_matches_high_din_two_cycles_back: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!$initstate && !$past($initstate) && (dout == 1'b1)) |-> $past(din, 2)
    );

endmodule