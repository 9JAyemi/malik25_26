module up_down_counter_sva (
    input logic up_down,
    input logic clear,
    input logic load,
    input logic [3:0] data_in,
    input logic clk,
    input logic [3:0] count_out
);

    // Active-low clear forces the counter to zero.
    check_clear_forces_zero: assert property (
        @(posedge clk) !clear |-> (count_out == 4'b0000)
    );

    // Load updates the counter with data_in on the next clock.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (!clear)
        load |=> (count_out == $past(data_in))
    );

    // Load has priority over up_down when both are asserted.
    check_load_priority_over_count: assert property (
        @(posedge clk) disable iff (!clear)
        (load && up_down) |=> (count_out == $past(data_in))
    );

    // Count increments by one when load is low and up_down is high.
    check_increment_when_up: assert property (
        @(posedge clk) disable iff (!clear)
        (!load && up_down) |=> (count_out == ($past(count_out) + 4'b0001))
    );

    // Count decrements by one when load is low and up_down is low.
    check_decrement_when_down: assert property (
        @(posedge clk) disable iff (!clear)
        (!load && !up_down) |=> (count_out == ($past(count_out) - 4'b0001))
    );

endmodule