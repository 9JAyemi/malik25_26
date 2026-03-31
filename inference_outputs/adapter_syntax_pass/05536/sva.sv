module up_down_counter_sva (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic reset,
    input logic [3:0] count,
    input logic [3:0] data_in
);

    // Reset forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'b0000)
    );

    // Load updates count with data_in on the next cycle.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (count == $past(data_in))
    );

    // Load has priority over up_down when both are asserted.
    check_load_priority_over_up_down: assert property (
        @(posedge clk) disable iff (reset)
        (load && up_down) |=> (count == $past(data_in))
    );

    // Count increments by one when load is low and up_down is high.
    check_increment_when_up: assert property (
        @(posedge clk) disable iff (reset)
        (!load && up_down) |=> (count == ($past(count) + 4'd1))
    );

    // Count decrements by one when load is low and up_down is low.
    check_decrement_when_down: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !up_down) |=> (count == ($past(count) - 4'd1))
    );

endmodule