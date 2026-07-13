module sync_counter_sva (
    input logic clk,
    input logic rst,
    input logic load,
    input logic [3:0] data,
    input logic [3:0] count
);

    // Reset forces the counter output to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 4'd0)
    );

    // When load is asserted, count updates with data on the next clock.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (rst) load |=> (count == $past(data))
    );

    // When load is deasserted, count increments by one on the next clock.
    check_increment_when_not_loading: assert property (
        @(posedge clk) disable iff (rst) !load |=> (count == ($past(count) + 4'd1))
    );

    // Incrementing from 4'hF wraps the 4-bit counter back to zero.
    check_wraps_after_max: assert property (
        @(posedge clk) disable iff (rst) (!load && (count == 4'hF)) |=> (count == 4'h0)
    );

    // Reset has priority over load when both are asserted.
    check_reset_priority_over_load: assert property (
        @(posedge clk) (rst && load) |-> (count == 4'd0)
    );

endmodule