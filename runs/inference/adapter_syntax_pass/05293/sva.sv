module sync_counter_sva (
    input logic clk,
    input logic rst,
    input logic load,
    input logic [3:0] data,
    input logic [3:0] count
);

    // Reset forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 4'd0)
    );

    // Reset has priority over load.
    check_reset_priority_over_load: assert property (
        @(posedge clk) (rst && load) |-> (count == 4'd0)
    );

    // Load updates count with data on the next cycle.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (rst) load |=> (count == $past(data))
    );

    // Without load, count increments by one on the next cycle.
    check_increment_when_not_loading: assert property (
        @(posedge clk) disable iff (rst) !load |=> (count == ($past(count) + 4'd1))
    );

    // Count wraps from 15 back to 0 when not loading.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (rst) (!load && (count == 4'hF)) |=> (count == 4'd0)
    );

endmodule