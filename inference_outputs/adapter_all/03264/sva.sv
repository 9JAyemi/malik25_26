module up_down_counter_sva (
    input logic up_down,
    input logic clear,
    input logic load,
    input logic [3:0] data_in,
    input logic clk,
    input logic [3:0] count_out
);

    // Active-low clear forces the counter output to zero.
    check_clear_forces_zero: assert property (
        @(posedge clk) !clear |-> (count_out == 4'b0000)
    );

    // Load captures data_in on the next clock when clear is high.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (!clear) load |=> (count_out == $past(data_in))
    );

    // With load low and up_down high, the counter increments by one.
    check_increment_when_up: assert property (
        @(posedge clk) disable iff (!clear) (!load && up_down) |=> (count_out == ($past(count_out) + 4'b0001))
    );

    // With load low and up_down low, the counter decrements by one.
    check_decrement_when_down: assert property (
        @(posedge clk) disable iff (!clear) (!load && !up_down) |=> (count_out == ($past(count_out) - 4'b0001))
    );

    // With load low and up_down high, the counter value changes.
    check_increment_changes_value: assert property (
        @(posedge clk) disable iff (!clear) (!load && up_down) |=> (count_out != $past(count_out))
    );

    // With load low and up_down low, the counter value changes.
    check_decrement_changes_value: assert property (
        @(posedge clk) disable iff (!clear) (!load && !up_down) |=> (count_out != $past(count_out))
    );

    // With load low and up_down high, the counter wraps from 4'hF to 4'h0.
    check_increment_wraps_from_max: assert property (
        @(posedge clk) disable iff (!clear) (!load && up_down && ($past(count_out) == 4'hF)) |=> (count_out == 4'h0)
    );

    // With load low and up_down low, the counter wraps from 4'h0 to 4'hF.
    check_decrement_wraps_from_min: assert property (
        @(posedge clk) disable iff (!clear) (!load && !up_down && ($past(count_out) == 4'h0)) |=> (count_out == 4'hF)
    );

endmodule