module counter4_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    property p_count_increments_when_enabled;
        logic [3:0] sampled_count;
        @(posedge clk iff !reset) disable iff (reset || $initstate)
            (enable, sampled_count = count) |=> @(posedge clk or posedge reset) (count == sampled_count + 4'd1);
    endproperty

    property p_count_holds_when_disabled;
        logic [3:0] sampled_count;
        @(posedge clk iff !reset) disable iff (reset || $initstate)
            (!enable, sampled_count = count) |=> @(posedge clk or posedge reset) (count == sampled_count);
    endproperty

    property p_clock_edge_with_reset_clears_count;
        @(posedge clk iff reset) disable iff ($initstate)
            1'b1 |=> @(posedge clk or posedge reset) (count == 4'd0);
    endproperty

    property p_async_reset_edge_clears_count;
        @(posedge reset) disable iff ($initstate)
            1'b1 |=> @(posedge clk or posedge reset) (count == 4'd0);
    endproperty

    // Count increments by one after a non-reset enabled clock edge.
    check_count_increments_when_enabled: assert property (p_count_increments_when_enabled);

    // Count holds its value after a non-reset disabled clock edge.
    check_count_holds_when_disabled: assert property (p_count_holds_when_disabled);

    // A clock edge taken while reset is high forces the count to zero.
    check_clock_edge_with_reset_clears_count: assert property (p_clock_edge_with_reset_clears_count);

    // An asynchronous reset edge forces the count to zero.
    check_async_reset_edge_clears_count: assert property (p_async_reset_edge_clears_count);

endmodule