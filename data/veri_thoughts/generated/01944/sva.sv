module dff_clear_reset_sva (
    input logic clock,
    input logic clr,       // active-low synchronous clear
    input logic clr_val,   // load enable when high and clr is high
    input logic d,
    input logic q
);
    // Clear low drives q to 0 on the next clock.
    check_clear_forces_zero_next: assert property (
        @(posedge clock) (!clr) |=> (q == 1'b0)
    );

    // Clear has priority over load when both are asserted.
    check_clear_priority_over_load: assert property (
        @(posedge clock) (!clr && clr_val) |=> (q == 1'b0)
    );

    // With clr high and clr_val high, q loads d on the next clock.
    check_load_updates_q: assert property (
        @(posedge clock) disable iff ($initstate || !clr) (clr && clr_val) |=> (q == $past(d))
    );

    // With clr high and clr_val low, q holds its value.
    check_hold_when_no_load: assert property (
        @(posedge clock) disable iff ($initstate || !clr) (clr && !clr_val) |=> (q == $past(q))
    );

    // Any change on q must be caused by prior clear or prior load.
    check_q_changes_only_on_clear_or_load: assert property (
        @(posedge clock) disable iff ($initstate) $changed(q) |-> $past((!clr) || (clr && clr_val))
    );

    // After a cycle with clr low, q must be 0 on this cycle.
    check_zero_after_prior_clear: assert property (
        @(posedge clock) disable iff ($initstate) $past(!clr) |-> (q == 1'b0)
    );

    // D changes are ignored when not loading (clr high, clr_val low).
    check_ignore_d_when_no_load: assert property (
        @(posedge clock) disable iff ($initstate || !clr) (!clr_val && $changed(d)) |=> (q == $past(q))
    );

    // Loading the same value leaves q unchanged across the boundary.
    check_load_same_value_no_change: assert property (
        @(posedge clock) disable iff ($initstate || !clr) (clr && clr_val && (d == q)) |=> (q == $past(q))
    );
endmodule