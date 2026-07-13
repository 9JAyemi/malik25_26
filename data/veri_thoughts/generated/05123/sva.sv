module my_module_sva (
    input logic clk,
    input logic din,
    input logic reset_n,
    input logic stdsync,
    input logic dout
);

    // During active-low reset, the registered output is low.
    check_reset_clears_dout: assert property (
        @(posedge clk) !reset_n |-> (dout == 1'b0)
    );

    // On the first clock after reset release, the sampled output is still low.
    check_reset_release_cycle_dout_low: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!$initstate && !$past(reset_n)) |-> (dout == 1'b0)
    );

    // Outside reset, dout reflects din from the previous clock edge.
    check_dout_is_one_cycle_delayed_din: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!$initstate && $past(reset_n)) |-> (dout == $past(din))
    );

    // If din is stable across active cycles, dout matches the current din.
    check_stable_din_matches_dout: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!$initstate && $past(reset_n) && (din == $past(din))) |-> (dout == din)
    );

    // If din toggles across active cycles, dout still shows the prior value.
    check_input_toggle_shows_pipeline_delay: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!$initstate && $past(reset_n) && (din != $past(din))) |-> (dout != din)
    );

endmodule