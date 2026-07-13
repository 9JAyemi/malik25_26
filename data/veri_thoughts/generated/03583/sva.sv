module up_counter_assertions (
    input logic       clk,
    input logic       rst,
    input logic       en,
    input logic [3:0] count
);

    // When reset is asserted low, the counter is cleared.
    reset_clears_count: assert property (
        @(posedge clk)
        !rst |-> (count == 4'd0)
    );

    // When enabled outside reset, the counter increments by one.
    enable_increments_count: assert property (
        @(posedge clk) disable iff (!rst)
        en |=> (count == ($past(count) + 4'd1))
    );

    // When not enabled outside reset, the counter holds its value.
    disable_holds_count: assert property (
        @(posedge clk) disable iff (!rst)
        !en |=> (count == $past(count))
    );

endmodule