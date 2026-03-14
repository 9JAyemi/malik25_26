module serial_rx_sva (
    input logic clk,
    input logic rst,       // Active-high synchronous reset
    input logic rx,
    input logic [7:0] data,
    input logic new_data
);
    // Clock: posedge clk. Logic: mixed (combinational next-state + sequential regs).

    ///// Reset behavior /////
    // new_data must be LOW during reset.
    check_reset_new_data_low: assert property (
        @(posedge clk) rst |-> (new_data == 1'b0)
    );
    // data holds its value during reset.
    check_reset_data_stable: assert property (
        @(posedge clk) rst |-> $stable(data)
    );

    ///// new_data pulse characteristics /////
    // new_data is a single-cycle pulse.
    check_new_data_single_cycle: assert property (
        @(posedge clk) disable iff (rst) new_data |=> !new_data
    );
    // No consecutive HIGH cycles on new_data.
    check_new_data_no_back_to_back_highs: assert property (
        @(posedge clk) disable iff (rst) !(new_data && $past(new_data))
    );

    ///// Data update behavior relative to new_data /////
    // When new_data rises, data updates in the same cycle.
    check_data_changes_at_new_data: assert property (
        @(posedge clk) disable iff (rst) $rose(new_data) |-> $changed(data)
    );
    // After new_data, data holds at least one cycle.
    check_data_stable_after_new_data: assert property (
        @(posedge clk) disable iff (rst) $rose(new_data) |=> $stable(data)
    );

    ///// Data shifting behavior (port-observable) /////
    // Any data change is a right shift with MSB loaded from previous rx.
    check_data_shift_on_change: assert property (
        @(posedge clk) disable iff (rst) $changed(data) |-> (data === { $past(rx), $past(data[7:1]) })
    );
    // MSB of data on change equals previous rx sample.
    check_msb_matches_rx_on_change: assert property (
        @(posedge clk) disable iff (rst) $changed(data) |-> (data[7] === $past(rx))
    );
    // On the new_data pulse, data reflects the same shift relation.
    check_data_shift_on_new_data: assert property (
        @(posedge clk) disable iff (rst) $rose(new_data) |-> (data === { $past(rx), $past(data[7:1]) })
    );

    ///// Idle/turnaround behavior /////
    // After new_data, data remains stable until the next falling edge of rx (start of next frame).
    check_data_stable_until_next_start: assert property (
        @(posedge clk) disable iff (rst) $rose(new_data) |-> $stable(data) until $fell(rx)
    );
    // new_data cannot assert in the same cycle as a falling edge on rx.
    check_no_immediate_new_data_after_rx_fall: assert property (
        @(posedge clk) disable iff (rst) $fell(rx) |-> !new_data
    );

endmodule