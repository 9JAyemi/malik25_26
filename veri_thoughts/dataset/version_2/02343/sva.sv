module counter_3bit_sva (
    input logic clk,
    input logic rst,
    input logic enable,
    input logic load,
    input logic [2:0] data_in,
    input logic [2:0] count
);
    // While reset is asserted low, count must be 0.
    reset_drives_zero: assert property (
        @(posedge clk) !rst |-> (count == 3'b000)
    );

    // When enable is LOW, count holds its value.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && !enable) |=> (count == $past(count))
    );

    // When enable and load are HIGH, next count equals data_in.
    load_updates_count: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && enable && load) |=> (count == $past(data_in))
    );

    // When enable is HIGH and load is LOW, next count increments by 1 (mod 8).
    increment_updates_count: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && enable && !load) |=> (count == ($past(count) + 3'd1))
    );

    // Any change to count requires enable to have been HIGH in the previous cycle.
    change_requires_enable: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && $changed(count)) |-> $past(enable)
    );

    // If load is HIGH but enable is LOW, count does not change.
    load_ignored_without_enable: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && !enable && load) |=> (count == $past(count))
    );

    // Increment wraps from 7 to 0 when enable is HIGH and load is LOW.
    wrap_on_increment_from_7: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && enable && !load && ($past(count) == 3'd7)) |=> (count == 3'd0)
    );

    // Increment does not produce 0 unless previous value was 7.
    no_zero_after_increment_unless_from_7: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && enable && !load && ($past(count) != 3'd7)) |=> (count != 3'd0)
    );

    // Increment always changes count (no self-loop when adding 1 mod 8).
    increment_always_changes_value: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && enable && !load) |=> (count != $past(count))
    );

    // Two consecutive increments add 2 (mod 8).
    two_step_increment_sequence: assert property (
        @(posedge clk) disable iff (!rst)
            (enable && !load) ##1 (enable && !load) |=> (count == ($past(count,2) + 3'd2))
    );
endmodule