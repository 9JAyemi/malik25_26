module strobe_gen_sva (
    input logic clock,
    input logic reset,
    input logic enable,
    input logic [7:0] rate,
    input logic strobe_in,
    input logic strobe,
    input logic [7:0] counter
);
    ///// Combinational strobe definition /////
    // strobe equals (counter==0) && enable && strobe_in.
    check_strobe_definition: assert property (
        @(posedge clock) (strobe == ((counter == 8'd0) && enable && strobe_in))
    );

    // strobe HIGH requires enable and strobe_in HIGH.
    strobe_requires_inputs: assert property (
        @(posedge clock) strobe |-> (enable && strobe_in)
    );

    // enable LOW forces strobe LOW.
    enable_low_forces_strobe_low: assert property (
        @(posedge clock) (!enable) |-> (strobe == 1'b0)
    );

    // strobe_in LOW forces strobe LOW.
    strobe_in_low_forces_strobe_low: assert property (
        @(posedge clock) (!strobe_in) |-> (strobe == 1'b0)
    );

    // strobe HIGH implies counter is zero.
    strobe_implies_counter_zero: assert property (
        @(posedge clock) strobe |-> (counter == 8'd0)
    );

    // When counter is zero and inputs are HIGH, strobe is HIGH.
    zero_counter_inputs_high_implies_strobe: assert property (
        @(posedge clock) (enable && strobe_in && (counter == 8'd0)) |-> strobe
    );

    ///// Counter update behavior /////
    // On reset, counter clears to zero on next cycle.
    counter_clears_on_reset: assert property (
        @(posedge clock) reset |=> (counter == 8'd0)
    );

    // When enable is LOW, counter clears to zero on next cycle.
    counter_clears_when_disabled: assert property (
        @(posedge clock) (!reset && !enable) |=> (counter == 8'd0)
    );

    // With enable HIGH and strobe_in LOW, counter holds its value.
    counter_holds_when_strobe_in_low: assert property (
        @(posedge clock) disable iff (reset) (enable && !strobe_in) |=> (counter == $past(counter))
    );

    // With enable and strobe_in HIGH and counter non-zero, counter decrements by one.
    counter_decrements_when_nonzero: assert property (
        @(posedge clock) disable iff (reset) (enable && strobe_in && (counter != 8'd0)) |=> (counter == $past(counter) - 8'd1)
    );

    // With enable and strobe_in HIGH and counter zero, counter loads rate.
    counter_loads_rate_when_zero: assert property (
        @(posedge clock) disable iff (reset) (enable && strobe_in && (counter == 8'd0)) |=> (counter == rate)
    );

    // When strobe is HIGH, counter loads rate on next cycle.
    strobe_implies_load_rate_next: assert property (
        @(posedge clock) disable iff (reset) strobe |=> (counter == rate)
    );
endmodule