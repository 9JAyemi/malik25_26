module counter_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic [3:0] data,
    input logic [3:0] count
);

    // Active-low reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !reset |-> (count == 4'b0000)
    );

    // When load is high, count updates to the sampled data value.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (!reset)
        load |=> (count == $past(data))
    );

    // When load is low, count increments by one on the next cycle.
    check_increment_when_not_loading: assert property (
        @(posedge clk) disable iff (!reset)
        !load |=> (count == ($past(count) + 4'd1))
    );

    // Incrementing from 4'hF wraps the counter back to zero.
    check_wraps_from_max: assert property (
        @(posedge clk) disable iff (!reset)
        (!load && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule