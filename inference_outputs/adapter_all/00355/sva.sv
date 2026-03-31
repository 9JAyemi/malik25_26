module m_pc_reg_sva (
    input logic [7:0] r_bus_addr_out,
    input logic [7:0] w_bus_addr_in,
    input logic w_clock,
    input logic w_reset
);
    // Clock: w_clock (posedge). Reset: w_reset (synchronous, active-high). Sequential register: r_bus_addr_out <= (w_reset ? 8'h00 : w_bus_addr_in).

    // On reset, next cycle r_bus_addr_out must be 0.
    reset_clears_next: assert property (
        @(posedge w_clock) w_reset |=> (r_bus_addr_out == 8'h00)
    );

    // When not in reset, next cycle r_bus_addr_out equals current w_bus_addr_in.
    capture_when_not_reset: assert property (
        @(posedge w_clock) disable iff (w_reset) 1'b1 |=> (r_bus_addr_out == $past(w_bus_addr_in))
    );

    // If not in reset and w_bus_addr_in is stable, r_bus_addr_out remains stable next cycle.
    stable_when_input_stable: assert property (
        @(posedge w_clock) disable iff (w_reset) $stable(w_bus_addr_in) |=> $stable(r_bus_addr_out)
    );

    // If not in reset and w_bus_addr_in changes, r_bus_addr_out changes next cycle.
    change_propagates_when_not_reset: assert property (
        @(posedge w_clock) disable iff (w_reset) $changed(w_bus_addr_in) |=> $changed(r_bus_addr_out)
    );

    // If not in reset and w_bus_addr_in changes, r_bus_addr_out equals the prior w_bus_addr_in value.
    change_matches_prior_input: assert property (
        @(posedge w_clock) disable iff (w_reset) $changed(w_bus_addr_in) |=> (r_bus_addr_out == $past(w_bus_addr_in))
    );

    // If not in reset and w_bus_addr_in is stable, r_bus_addr_out equals the prior w_bus_addr_in value.
    stable_output_matches_prior_input: assert property (
        @(posedge w_clock) disable iff (w_reset) $stable(w_bus_addr_in) |=> (r_bus_addr_out == $past(w_bus_addr_in))
    );

    // If not in reset and w_bus_addr_in changes, r_bus_addr_out differs from the current w_bus_addr_in value.
    change_differs_from_current_input: assert property (
        @(posedge w_clock) disable iff (w_reset) $changed(w_bus_addr_in) |=> (r_bus_addr_out != w_bus_addr_in)
    );

    // If not in reset and w_bus_addr_in changes, r_bus_addr_out differs from the prior r_bus_addr_out value.
    change_differs_from_prior_output: assert property (
        @(posedge w_clock) disable iff (w_reset) $changed(w_bus_addr_in) |=> (r_bus_addr_out != $past(r_bus_addr_out))
    );

    // If not in reset and w_bus_addr_in changes, r_bus_addr_out changes on the next cycle.
    change_propagates_next_cycle: assert property (
        @(posedge w_clock) disable iff (w_reset) $changed(w_bus_addr_in) |=> $changed(r_bus_addr_out)
    );

    // If not in reset and w_bus_addr_in changes, r_bus_addr_out equals the prior w_bus_addr_in value on the next cycle.
    change_updates_next_cycle: assert property (
        @(posedge w_clock) disable iff (w_reset) $changed(w_bus_addr_in) |=> (r_bus_addr_out == $past(w_bus_addr_in))
    );
endmodule