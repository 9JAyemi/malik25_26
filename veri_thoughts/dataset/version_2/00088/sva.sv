module and_delayed_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic out,
    input logic delayed_a,
    input logic delayed_b
);

    // Clock: clk.
    // Reset: none.
    // Sequential behavior: a and b are registered, then out registers their AND.

    // delayed_a captures a on the next clock.
    check_delayed_a_high_capture: assert property (
        @(posedge clk) a |=> delayed_a
    );

    // delayed_a captures a low value on the next clock.
    check_delayed_a_low_capture: assert property (
        @(posedge clk) !a |=> !delayed_a
    );

    // delayed_b captures b on the next clock.
    check_delayed_b_high_capture: assert property (
        @(posedge clk) b |=> delayed_b
    );

    // delayed_b captures a low value on the next clock.
    check_delayed_b_low_capture: assert property (
        @(posedge clk) !b |=> !delayed_b
    );

    // out goes high one clock after both delayed inputs are high.
    check_out_high_from_delayed_and: assert property (
        @(posedge clk) (delayed_a && delayed_b) |=> out
    );

    // out goes low one clock after either delayed input is low.
    check_out_low_from_delayed_zero: assert property (
        @(posedge clk) (!delayed_a || !delayed_b) |=> !out
    );

    // High inputs produce a high out after two clocks.
    check_out_high_two_cycles_after_inputs_high: assert property (
        @(posedge clk) (a && b) |-> ##2 out
    );

    // A low a forces out low after two clocks.
    check_out_low_two_cycles_after_a_low: assert property (
        @(posedge clk) !a |-> ##2 !out
    );

    // A low b forces out low after two clocks.
    check_out_low_two_cycles_after_b_low: assert property (
        @(posedge clk) !b |-> ##2 !out
    );

endmodule