module d_ff_with_set_clear_sva (
    input logic clk,
    input logic d,
    input logic set,
    input logic clear,
    input logic q
);

    // q must match the prior cycle's clear/set/data priority.
    check_state_update_function: assert property (
        @(posedge clk)
        !$initstate |-> (q == ($past(clear) ? 1'b0 : ($past(set) ? 1'b1 : $past(d))))
    );

    // clear forces q low on the following sampled cycle.
    check_clear_forces_zero: assert property (
        @(posedge clk)
        clear |=> (q == 1'b0)
    );

    // clear overrides set when both are asserted.
    check_clear_priority_over_set: assert property (
        @(posedge clk)
        (clear && set) |=> (q == 1'b0)
    );

    // set drives q high when clear is low.
    check_set_forces_one_when_clear_low: assert property (
        @(posedge clk)
        (!clear && set) |=> (q == 1'b1)
    );

    // d is captured when both control inputs are low.
    check_data_capture_when_controls_low: assert property (
        @(posedge clk)
        (!clear && !set) |=> (q == $past(d))
    );

endmodule