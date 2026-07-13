module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic load,
    input logic [3:0] data_in,
    input logic [3:0] count
);
    // Reset drives count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'b0000)
    );

    // When enable is LOW, count holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (!enable) |-> (count == $past(count))
    );

    // With enable and load HIGH, count takes data_in on the same edge.
    check_load_updates_immediately: assert property (
        @(posedge clk) disable iff (reset) (enable && load) |-> (count == data_in)
    );

    // With enable HIGH and load LOW, count increments by 1 (modulo 16).
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset) (enable && !load) |-> (count == $past(count) + 4'd1)
    );

    // Increment path wraps from 0xF to 0x0.
    check_increment_wraparound: assert property (
        @(posedge clk) disable iff (reset) (enable && !load && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // Any change to count (outside reset) requires enable HIGH.
    check_change_requires_enable: assert property (
        @(posedge clk) disable iff (reset) $changed(count) |-> enable
    );

    // Increment path must change the value (cannot hold).
    check_increment_causes_change: assert property (
        @(posedge clk) disable iff (reset) (enable && !load) |-> (count != $past(count))
    );
endmodule