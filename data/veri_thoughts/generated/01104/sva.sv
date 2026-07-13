module final_output_sva (
    input logic clk,
    input logic reset,
    input logic d,
    input logic rise,
    input logic down,
    input logic q_out
);
    // Clock: clk; Reset: reset (active-high synchronous).
    // Sequential flop: rise sets 1, else if down sets 0, else hold; q_out mirrors flop.

    // During reset, output is forced low.
    reset_forces_zero: assert property (
        @(posedge clk) reset |-> (q_out == 1'b0)
    );

    // Full next-state function when not in reset.
    functional_next_state: assert property (
        @(posedge clk) disable iff (reset)
            q_out == ( rise ? 1'b1 : ( down ? 1'b0 : $past(q_out) ) )
    );

    // If rise is asserted, output becomes 1 (independent of down).
    check_rise_sets_one: assert property (
        @(posedge clk) disable iff (reset) rise |-> (q_out == 1'b1)
    );

    // If down is asserted without rise, output becomes 0.
    check_down_clears_when_no_rise: assert property (
        @(posedge clk) disable iff (reset) (down && !rise) |-> (q_out == 1'b0)
    );

    // If neither control is asserted, output holds its value.
    check_hold_when_no_ctrl: assert property (
        @(posedge clk) disable iff (reset) (!rise && !down) |-> $stable(q_out)
    );

    // When both controls are asserted, rise has priority and output is 1.
    check_priority_rise_over_down: assert property (
        @(posedge clk) disable iff (reset) (rise && down) |-> (q_out == 1'b1)
    );

    // A 0->1 transition on output can only occur due to rise when not in reset.
    check_output_rise_requires_rise: assert property (
        @(posedge clk) disable iff (reset) $rose(q_out) |-> rise
    );

    // A 1->0 transition on output (outside reset) can only occur due to down without rise.
    check_output_fall_requires_down_no_rise: assert property (
        @(posedge clk) disable iff (reset) $fell(q_out) |-> (down && !rise)
    );
endmodule