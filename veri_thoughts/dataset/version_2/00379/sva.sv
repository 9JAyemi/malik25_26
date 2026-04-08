module dff2_sva (
    input logic [1:0] d,
    input logic       clk,
    input logic       clrn,
    input logic [1:0] q
);

    // If reset is low at a clock edge, q must be zero.
    check_reset_low_holds_q_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        !clrn |-> (q == 2'b00)
    );

    // If reset is observed to fall between clocks, q is zero at the next clock.
    check_sampled_reset_fall_clears_q: assert property (
        @(posedge clk) disable iff ($initstate)
        $fell(clrn) |-> (q == 2'b00)
    );

    // On the first clock after reset release, q is still zero before recapturing d.
    check_reset_release_starts_from_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        $rose(clrn) |-> (q == 2'b00)
    );

    // Outside reset, q is either the prior-cycle d or zero from an async clear.
    check_q_is_prev_d_or_zero: assert property (
        @(posedge clk) disable iff (!clrn || $initstate)
        1'b1 |-> ((q == $past(d)) || (q == 2'b00))
    );

    // A nonzero q must match the prior-cycle d.
    check_nonzero_q_matches_prev_d: assert property (
        @(posedge clk) disable iff (!clrn || $initstate)
        (q != 2'b00) |-> (q == $past(d))
    );

    // If the prior-cycle d was zero, q must be zero.
    check_prev_zero_d_leads_to_zero_q: assert property (
        @(posedge clk) disable iff (!clrn || $initstate)
        ($past(d) == 2'b00) |-> (q == 2'b00)
    );

    // A nonzero q cannot immediately follow a sampled reset-low cycle.
    check_nonzero_q_requires_prev_reset_high: assert property (
        @(posedge clk) disable iff (!clrn || $initstate)
        (q != 2'b00) |-> $past(clrn)
    );

    // If q changes to a nonzero value, it must come from the prior-cycle d.
    check_q_change_to_nonzero_matches_prev_d: assert property (
        @(posedge clk) disable iff (!clrn || $initstate)
        ($changed(q) && (q != 2'b00)) |-> (q == $past(d))
    );

endmodule