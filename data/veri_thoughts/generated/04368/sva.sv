module binary_up_down_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       up_down,
    input logic       clear,
    input logic       load,
    input logic [3:0] data_in,
    input logic [3:0] count
);

    // After reset deasserts, count remains zero until the next clocked update.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> (count == 4'b0000)
    );

    // Clear has highest priority and forces count to zero.
    check_clear_forces_zero: assert property (
        @(posedge clk) disable iff (reset)
        clear |=> (count == 4'b0000)
    );

    // Load updates count from data_in when clear is low.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (reset)
        (!clear && load) |=> (count == $past(data_in))
    );

    // Count increments when clear and load are low and up_down is high.
    check_increment_behavior: assert property (
        @(posedge clk) disable iff (reset)
        (!clear && !load && up_down) |=> (count == ($past(count) + 4'd1))
    );

    // Count decrements when clear and load are low and up_down is low.
    check_decrement_behavior: assert property (
        @(posedge clk) disable iff (reset)
        (!clear && !load && !up_down) |=> (count == ($past(count) - 4'd1))
    );

endmodule