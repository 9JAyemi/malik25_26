module spll_sva (
    input logic areset,
    input logic inclk0,
    input logic c0,
    input logic c1,
    input logic locked
);
    ///// Reset behavior /////
    // While reset is asserted (low), outputs drive c0=0, c1=1, locked=0.
    check_reset_values: assert property (
        @(posedge inclk0) !areset |-> (c0 == 1'b0) && (c1 == 1'b1) && (locked == 1'b0)
    );

    ///// Locked relation /////
    // locked equals c0 AND NOT c1 every active cycle.
    check_locked_matches_outputs: assert property (
        @(posedge inclk0) disable iff (!areset) locked == (c0 & ~c1)
    );

    ///// State transitions /////
    // From state 00, next state is 01 and locked=0.
    check_transition_from_00: assert property (
        @(posedge inclk0) disable iff (!areset)
            (c0 == 1'b0 && c1 == 1'b0) |=> (c0 == 1'b0 && c1 == 1'b1 && locked == 1'b0)
    );

    // From state 01, next state is 11 and locked=0.
    check_transition_from_01: assert property (
        @(posedge inclk0) disable iff (!areset)
            (c0 == 1'b0 && c1 == 1'b1) |=> (c0 == 1'b1 && c1 == 1'b1 && locked == 1'b0)
    );

    // From state 11, next state is 10 and locked=1.
    check_transition_from_11: assert property (
        @(posedge inclk0) disable iff (!areset)
            (c0 == 1'b1 && c1 == 1'b1) |=> (c0 == 1'b1 && c1 == 1'b0 && locked == 1'b1)
    );

    // From state 10, next state is 00 and locked=0.
    check_transition_from_10: assert property (
        @(posedge inclk0) disable iff (!areset)
            (c0 == 1'b1 && c1 == 1'b0) |=> (c0 == 1'b0 && c1 == 1'b0 && locked == 1'b0)
    );

    ///// Locked pulse behavior /////
    // locked cannot stay HIGH for two consecutive cycles.
    check_locked_single_cycle_pulse: assert property (
        @(posedge inclk0) disable iff (!areset) locked |=> !locked
    );

    ///// Post-reset sequencing /////
    // On the first cycle after reset deasserts, state is 11 with locked=0.
    check_first_cycle_after_reset_deassert: assert property (
        @(posedge inclk0) disable iff (!areset) $rose(areset) |-> (c0 == 1'b1) && (c1 == 1'b1) && (locked == 1'b0)
    );

    ///// Locked next-state when not in 11 /////
    // If current state is not 11, next locked is 0.
    check_locked_next_zero_when_not_11: assert property (
        @(posedge inclk0) disable iff (!areset)
            !(c0 && c1) |=> (locked == 1'b0)
    );
endmodule