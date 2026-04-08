module global_reset_sva (
    input logic       clock_i,
    input logic       forced_reset_i,
    input logic       n_reset_o,
    input logic       n_limited_reset_o,
    input logic [7:0] reset_counter
);

    // n_limited_reset_o decodes reset_counter <= 1.
    check_limited_reset_decode: assert property (
        @(negedge clock_i) n_limited_reset_o == (reset_counter <= 8'd1)
    );

    // n_reset_o decodes reset_counter <= 1 and forced_reset_i.
    check_reset_decode: assert property (
        @(negedge clock_i) n_reset_o == ((reset_counter <= 8'd1) & !forced_reset_i)
    );

    // n_reset_o is n_limited_reset_o masked by forced_reset_i.
    check_reset_is_masked_limited_reset: assert property (
        @(negedge clock_i) n_reset_o == (n_limited_reset_o & !forced_reset_i)
    );

    // forced_reset_i always drives n_reset_o low.
    check_forced_reset_forces_n_reset_low: assert property (
        @(negedge clock_i) forced_reset_i |-> !n_reset_o
    );

    // A nonzero counter increments by one on each falling edge.
    check_counter_increments_while_nonzero: assert property (
        @(negedge clock_i) (reset_counter != 8'd0) |=> (reset_counter == ($past(reset_counter) + 8'd1))
    );

    // Once the counter reaches zero, it stays at zero.
    check_counter_holds_at_zero: assert property (
        @(negedge clock_i) (reset_counter == 8'd0) |=> (reset_counter == 8'd0)
    );

    // The counter wraps from 8'hFF to 8'h00.
    check_counter_wraps_to_zero: assert property (
        @(negedge clock_i) (reset_counter == 8'hFF) |=> (reset_counter == 8'h00)
    );

    // Counts above 1 force both reset outputs low.
    check_midcount_outputs_low: assert property (
        @(negedge clock_i) (reset_counter > 8'd1) |-> (!n_limited_reset_o && !n_reset_o)
    );

endmodule

bind global_reset global_reset_sva global_reset_sva_i (
    .clock_i(clock_i),
    .forced_reset_i(forced_reset_i),
    .n_reset_o(n_reset_o),
    .n_limited_reset_o(n_limited_reset_o),
    .reset_counter(reset_counter)
);