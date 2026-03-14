module gray_counter_sva (
    input logic clk,
    input logic reset, // Synchronous active-high reset
    input logic up_down,
    input logic enable,
    input logic [1:0] counter_out,
    input logic [1:0] gray_out
);

    ///// Counter sequencing rules /////
    // On a reset clock edge, counter_out synchronously clears to 0.
    reset_clears_counter: assert property (
        @(posedge clk) reset |-> (counter_out == 2'b00)
    );

    // When enable is LOW, counter_out holds its value to the next cycle.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (!enable) |=> (counter_out == $past(counter_out))
    );

    // When enable is HIGH and up_down is HIGH, next counter_out increments by 1 (mod 4).
    increment_when_up: assert property (
        @(posedge clk) disable iff (reset) (enable && up_down) |=> (counter_out == $past(counter_out) + 2'b01)
    );

    // When enable is HIGH and up_down is LOW, next counter_out decrements by 1 (mod 4).
    decrement_when_down: assert property (
        @(posedge clk) disable iff (reset) (enable && !up_down) |=> (counter_out == $past(counter_out) - 2'b01)
    );

    // When enable is HIGH, the counter must change value on the next cycle.
    enabled_causes_change: assert property (
        @(posedge clk) disable iff (reset) enable |=> (counter_out != $past(counter_out))
    );

    // For any enabled cycle, the next value matches the selected direction.
    enabled_update_matches_dir: assert property (
        @(posedge clk) disable iff (reset) enable |=> (
            (up_down && (counter_out == $past(counter_out) + 2'b01)) ||
            (!up_down && (counter_out == $past(counter_out) - 2'b01))
        )
    );

    ///// Gray converter mapping (combinational) /////
    // Mapping for counter_out == 2'b00.
    gray_map_00: assert property (
        @(posedge clk) disable iff (reset) (counter_out == 2'b00) |-> (gray_out == 2'b00)
    );

    // Mapping for counter_out == 2'b01.
    gray_map_01: assert property (
        @(posedge clk) disable iff (reset) (counter_out == 2'b01) |-> (gray_out == 2'b01)
    );

    // Mapping for counter_out == 2'b10.
    gray_map_10: assert property (
        @(posedge clk) disable iff (reset) (counter_out == 2'b10) |-> (gray_out == 2'b10)
    );

    // Mapping for counter_out == 2'b11.
    gray_map_11: assert property (
        @(posedge clk) disable iff (reset) (counter_out == 2'b11) |-> (gray_out == 2'b11)
    );

endmodule