module top_sva #(
    parameter int N = 10
) (
    input logic clk,
    input logic rst,
    input logic out,
    input logic outclk_0,
    input logic outclk_1,
    input logic locked,
    input logic [N-1:0] phase_accumulator
);

    // Top output is a direct copy of outclk_0.
    check_out_mirrors_outclk0: assert property (
        @(posedge clk) disable iff (rst)
        out == outclk_0
    );

    // Reset clears the counter, both output clocks, lock, and top output.
    check_reset_clears_pll_state: assert property (
        @(posedge clk)
        rst |-> ((phase_accumulator == '0) &&
                 (outclk_0 == 1'b0) &&
                 (outclk_1 == 1'b0) &&
                 (locked   == 1'b0) &&
                 (out      == 1'b0))
    );

    // The phase accumulator stays within the implemented 0 to N-1 range.
    check_phase_accumulator_range: assert property (
        @(posedge clk) disable iff (rst)
        phase_accumulator <= (N-1)
    );

    // Below terminal count, the phase accumulator increments by one.
    check_phase_accumulator_increment: assert property (
        @(posedge clk) disable iff (rst)
        (phase_accumulator != (N-1)) |=> (phase_accumulator == ($past(phase_accumulator) + 1'b1))
    );

    // At terminal count, the phase accumulator wraps back to zero.
    check_phase_accumulator_wrap: assert property (
        @(posedge clk) disable iff (rst)
        (phase_accumulator == (N-1)) |=> (phase_accumulator == '0)
    );

    // Before wrap, both output clocks hold their values.
    check_outputs_hold_before_wrap: assert property (
        @(posedge clk) disable iff (rst)
        (phase_accumulator != (N-1)) |=> ((outclk_0 == $past(outclk_0)) &&
                                          (outclk_1 == $past(outclk_1)))
    );

    // At wrap, both output clocks toggle together.
    check_outputs_toggle_on_wrap: assert property (
        @(posedge clk) disable iff (rst)
        (phase_accumulator == (N-1)) |=> ((outclk_0 != $past(outclk_0)) &&
                                          (outclk_1 != $past(outclk_1)))
    );

    // The lock signal is asserted after a terminal-count event.
    check_locked_asserts_on_wrap: assert property (
        @(posedge clk) disable iff (rst)
        (phase_accumulator == (N-1)) |=> (locked == 1'b1)
    );

    // Without a wrap event, the lock signal holds its previous value.
    check_locked_holds_without_wrap: assert property (
        @(posedge clk) disable iff (rst)
        (phase_accumulator != (N-1)) |=> (locked == $past(locked))
    );

    // Once asserted, lock remains high until reset.
    check_locked_sticky: assert property (
        @(posedge clk) disable iff (rst)
        locked |=> locked
    );

    // The two generated clocks always match because they toggle together.
    check_output_clocks_match: assert property (
        @(posedge clk) disable iff (rst)
        outclk_0 == outclk_1
    );

    // A lock rising edge can only follow a terminal-count cycle.
    check_locked_rise_only_after_wrap: assert property (
        @(posedge clk) disable iff (rst)
        $rose(locked) |-> ($past(phase_accumulator) == (N-1))
    );

    // An outclk_0 toggle can only follow a terminal-count cycle.
    check_outclk0_toggle_only_after_wrap: assert property (
        @(posedge clk) disable iff (rst)
        $changed(outclk_0) |-> ($past(phase_accumulator) == (N-1))
    );

endmodule