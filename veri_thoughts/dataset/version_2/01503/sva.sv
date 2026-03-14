module fsm_rising_edge_counter_sva (
    input logic clk,
    input logic in,
    input logic [2:0] count,
    input logic d_last,
    input logic [1:0] state
);
    // Mirror DUT state encodings
    localparam [1:0] IDLE  = 2'b00;
    localparam [1:0] COUNT = 2'b01;

    // d_last captures previous value of in each cycle.
    check_d_last_tracks_in_prev: assert property (
        @(posedge clk) !$isunknown($past(in)) |-> (d_last == $past(in))
    );

    // In IDLE, a rising edge (in && !d_last) causes next state COUNT and count reset to 0.
    check_idle_rise_enters_count_and_resets: assert property (
        @(posedge clk) (state == IDLE) && (in && !d_last) |=> (state == COUNT) && (count == 3'd0)
    );

    // In COUNT with no rising edge, next state goes to IDLE.
    check_count_no_rise_goes_idle: assert property (
        @(posedge clk) (state == COUNT) && !(in && !d_last) |=> (state == IDLE)
    );

    // In COUNT with a rising edge and count != 4, next cycle increments count and stays in COUNT.
    check_count_rise_incr_and_stay: assert property (
        @(posedge clk) (state == COUNT) && (in && !d_last) && (count != 3'd4) |=> (state == COUNT) && (count == $past(count) + 1)
    );

    // In COUNT with a rising edge and count == 4, next cycle goes to IDLE.
    check_count_rise_at4_goes_idle: assert property (
        @(posedge clk) (state == COUNT) && (in && !d_last) && (count == 3'd4) |=> (state == IDLE)
    );

    // Entering COUNT must come from IDLE on a rising edge.
    check_enter_count_requires_idle_rise: assert property (
        @(posedge clk) (state == COUNT) && ($past(state) != COUNT) |-> ($past(state) == IDLE) && $past(in) && !$past(d_last)
    );

    // Staying in COUNT across cycles requires a prior rising edge and count != 4.
    check_stay_in_count_requires_prev_rise_not4: assert property (
        @(posedge clk) ($past(state) == COUNT) && (state == COUNT) |-> $past(in) && !$past(d_last) && ($past(count) != 3'd4)
    );

    // From IDLE with no rising edge, remain in IDLE.
    check_idle_stays_idle_without_rise: assert property (
        @(posedge clk) ($past(state) == IDLE) && (!$past(in) || $past(d_last)) |-> (state == IDLE)
    );

    // Any change to count must be due to the defined update cases.
    check_count_changes_only_when_expected: assert property (
        @(posedge clk)
            (!$isunknown($past(count))) && (count != $past(count)) |-> 
            (
                // From IDLE on rising: count becomes 0
                (($past(state) == IDLE)  && $past(in) && !$past(d_last) && (count == 3'd0))
                ||
                // From COUNT on rising when count != 4: increment
                (($past(state) == COUNT) && $past(in) && !$past(d_last) && ($past(count) != 3'd4) && (count == $past(count) + 1))
            )
    );

    // Leaving COUNT to IDLE must be due to either no rising edge or rising with count==4.
    check_count_to_idle_has_valid_cause: assert property (
        @(posedge clk) ($past(state) == COUNT) && (state == IDLE) |-> 
            (!$past(in) || $past(d_last)) || ( $past(in) && !$past(d_last) && ($past(count) == 3'd4) )
    );

endmodule