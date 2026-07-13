module my_register_sva (
    input logic clk,
    input logic ena,
    input logic d,
    input logic clrn, // active-low synchronous clear
    input logic prn,  // active-low synchronous preset
    input logic q
);

    ///// Reset behavior /////
    // When clear is asserted low, q must be 0 on the next clock.
    check_clear_forces_zero: assert property (
        @(posedge clk) (clrn == 1'b0) |=> (q == 1'b0)
    );

    // When preset is asserted low (and clear is high), q must be 1 on the next clock.
    check_preset_sets_one: assert property (
        @(posedge clk) (clrn == 1'b1 && prn == 1'b0) |=> (q == 1'b1)
    );

    // If both clear and preset are low, clear has priority and q must be 0 next clock.
    check_clear_overrides_preset: assert property (
        @(posedge clk) (clrn == 1'b0 && prn == 1'b0) |=> (q == 1'b0)
    );

    ///// Enable/hold behavior when no resets /////
    // With no resets and enable high, q loads d on the next clock.
    check_enable_loads_d_when_no_resets: assert property (
        @(posedge clk) disable iff (!clrn || !prn) (ena == 1'b1) |=> (q == $past(d))
    );

    // With no resets and enable low, q holds its previous value.
    check_hold_when_disabled_when_no_resets: assert property (
        @(posedge clk) disable iff (!clrn || !prn) (ena == 1'b0) |=> (q == $past(q))
    );

    // With no resets, any change in q must be caused by enable being high in the prior cycle.
    check_change_requires_enable_when_no_resets: assert property (
        @(posedge clk) disable iff (!clrn || !prn)
            ($past(clrn == 1'b1 && prn == 1'b1) && (q != $past(q))) |-> ($past(ena) == 1'b1)
    );

    // With no resets, the full next-state function matches: q_next = ena ? d : q.
    check_next_state_matches_spec_when_no_resets: assert property (
        @(posedge clk) disable iff (!clrn || !prn)
            1'b1 |=> (q == ($past(ena) ? $past(d) : $past(q)))
    );

endmodule