module baud_generator_sva (
    input logic clk,
    input logic pulse,
    input logic [15:0] counter,
    input logic [15:0] compare_value
);
    ///// Parameter register behavior /////
    // compare_value must remain constant after the first cycle.
    hold_compare_value_constant: assert property (
        @(posedge clk) $past(1'b1) |-> (compare_value == $past(compare_value))
    );

    ///// Counter update rules /////
    // Counter update is either reset to 0 or increments by 1 each cycle.
    counter_update_is_reset_or_inc: assert property (
        @(posedge clk) $past(1'b1) |-> (counter == 16'd0 || counter == ($past(counter) + 16'd1))
    );

    // When last-cycle counter equaled compare_value, counter resets to 0.
    counter_resets_on_match: assert property (
        @(posedge clk) ($past(1'b1) && ($past(counter) == compare_value)) |-> (counter == 16'd0)
    );

    // When last-cycle counter did not equal compare_value, counter increments by 1.
    counter_increments_on_no_match: assert property (
        @(posedge clk) ($past(1'b1) && ($past(counter) != compare_value)) |-> (counter == ($past(counter) + 16'd1))
    );

    ///// Pulse generation rules /////
    // Pulse reflects whether last-cycle counter matched compare_value.
    pulse_reflects_prev_compare: assert property (
        @(posedge clk) $past(1'b1) |-> (pulse == ($past(counter) == compare_value))
    );

    // If pulse is high, counter must be 0 in the same cycle.
    pulse_implies_counter_zero: assert property (
        @(posedge clk) pulse |-> (counter == 16'd0)
    );

    ///// Corner cases due to 16-bit arithmetic /////
    // If counter becomes 0 without a compare match, the previous value must have been 16'hFFFF (overflow wrap).
    overflow_to_zero_requires_ffff: assert property (
        @(posedge clk) ($past(1'b1) && ($past(counter) != compare_value) && (counter == 16'd0)) |-> ($past(counter) == 16'hFFFF)
    );

    // If counter is 0 this cycle, it must be due to either a compare match or overflow from 16'hFFFF.
    counter_zero_causes: assert property (
        @(posedge clk) ($past(1'b1) && (counter == 16'd0)) |-> (($past(counter) == compare_value) || ($past(counter) == 16'hFFFF))
    );
endmodule

bind baud_generator baud_generator_sva u_baud_generator_sva (
    .clk(clk),
    .pulse(pulse),
    .counter(counter),
    .compare_value(compare_value)
);