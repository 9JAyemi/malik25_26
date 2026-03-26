module heartbeat_sva(
    input logic        clk_i,
    input logic        nreset_i,
    input logic        heartbeat_o,
    input logic [26:0] cntr,
    input logic        heartbeat
);

    // Clock is clk_i.
    // Reset is synchronous active-low nreset_i.
    // State is sequential; heartbeat_o is a combinational mirror of heartbeat.
    // cntr clears at 5,000,000 and toggles heartbeat on that event.

    // The output always mirrors the internal heartbeat register.
    check_output_matches_heartbeat: assert property (
        @(posedge clk_i) (heartbeat_o == heartbeat)
    );

    // A reset cycle clears the counter and heartbeat by the next clock.
    check_reset_clears_state: assert property (
        @(posedge clk_i) (!nreset_i) |=> ((cntr == 27'd0) && (heartbeat == 1'b0))
    );

    // If reset stays asserted, state and output remain low.
    check_reset_holds_zero_values: assert property (
        @(posedge clk_i) ((!nreset_i) && $past(!nreset_i)) |-> ((cntr == 27'd0) && (heartbeat == 1'b0) && (heartbeat_o == 1'b0))
    );

    // Below the terminal count, the counter increments by one.
    check_counter_increments_before_wrap: assert property (
        @(posedge clk_i) disable iff (!nreset_i)
        (cntr != 27'd5000000) |=> (cntr == ($past(cntr) + 27'd1))
    );

    // Below the terminal count, the heartbeat register holds its value.
    check_heartbeat_stable_before_wrap: assert property (
        @(posedge clk_i) disable iff (!nreset_i)
        (cntr != 27'd5000000) |=> (heartbeat == $past(heartbeat))
    );

    // At the terminal count, the counter reloads to zero.
    check_counter_wraps_at_terminal_count: assert property (
        @(posedge clk_i) disable iff (!nreset_i)
        (cntr == 27'd5000000) |=> (cntr == 27'd0)
    );

    // At the terminal count, the heartbeat register toggles.
    check_heartbeat_toggles_at_terminal_count: assert property (
        @(posedge clk_i) disable iff (!nreset_i)
        (cntr == 27'd5000000) |=> (heartbeat == ~$past(heartbeat))
    );

endmodule