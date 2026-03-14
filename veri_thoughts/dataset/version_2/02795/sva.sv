module counter_sva (
    input logic clk,
    input logic LOAD,
    input logic RESET,      // Active-high synchronous reset
    input logic [1:0] DATA,
    input logic [1:0] Q
);
    // Clock: clk (posedge). Reset: RESET (active-high, synchronous).
    // Behavior: if RESET then Q<=0; else if LOAD then Q<=DATA; else Q<=Q+1 (2-bit wrap).

    // Synchronous reset drives Q to 0 on the next clock.
    reset_clears_q: assert property (
        @(posedge clk) RESET |=> (Q == 2'b00)
    );

    // Next-state matches RTL when not in reset: load has priority else increment.
    next_state_matches_rtl: assert property (
        @(posedge clk) disable iff (RESET)
            1'b1 |=> (Q == ($past(LOAD) ? $past(DATA) : ($past(Q) + 2'b01)))
    );

    // When LOAD is asserted (no reset), Q updates to DATA on the next clock.
    next_q_on_load: assert property (
        @(posedge clk) disable iff (RESET)
            LOAD |=> (Q == $past(DATA))
    );

    // When LOAD is deasserted (no reset), Q increments by 1 on the next clock.
    next_q_on_no_load_increment: assert property (
        @(posedge clk) disable iff (RESET)
            !LOAD |=> (Q == ($past(Q) + 2'b01))
    );

    // Increment wraps from 3 to 0 when LOAD is low (no reset).
    increment_wraps_at_3: assert property (
        @(posedge clk) disable iff (RESET)
            (!LOAD && (Q == 2'b11)) |=> (Q == 2'b00)
    );

    // With LOAD low for two cycles (no reset), Q increases by 2 over two clocks.
    two_cycle_increment_when_no_load: assert property (
        @(posedge clk) disable iff (RESET)
            (!LOAD ##1 !LOAD) |=> (Q == ($past(Q,2) + 2'd2))
    );

    // With LOAD high for two cycles (no reset), Q follows DATA from the immediately preceding cycle.
    two_consecutive_loads_follow_data: assert property (
        @(posedge clk) disable iff (RESET)
            (LOAD ##1 LOAD) |=> (Q == $past(DATA,1))
    );

    // LOAD followed by no-LOAD (no reset): Q becomes loaded DATA then increments next.
    load_then_increment: assert property (
        @(posedge clk) disable iff (RESET)
            (LOAD ##1 !LOAD) |=> (Q == ($past(DATA,2) + 2'b01))
    );

endmodule