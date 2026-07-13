module binary_counter_assertions (
    input logic       clk,
    input logic       rst,
    input logic       enable,
    input logic [3:0] count
);

    // Active-low reset forces count to zero.
    reset_forces_count_zero: assert property (
        @(posedge clk) !rst |-> (count == 4'b0000)
    );

    // When enabled, the counter increments by one on the next cycle.
    enable_branch_increments: assert property (
        @(posedge clk) disable iff (!rst)
        enable |=> (count == ($past(count) + 4'd1))
    );

    // When disabled below 15, the counter still increments by one.
    disabled_nonmax_branch_increments: assert property (
        @(posedge clk) disable iff (!rst)
        (!enable && (count != 4'hF)) |=> (count == ($past(count) + 4'd1))
    );

    // When disabled at 15, the counter wraps to zero on the next cycle.
    disabled_max_branch_wraps: assert property (
        @(posedge clk) disable iff (!rst)
        (!enable && (count == 4'hF)) |=> (count == 4'h0)
    );

    // Outside reset, the counter advances by one every cycle.
    counter_advances_each_cycle: assert property (
        @(posedge clk) disable iff (!rst)
        1'b1 |=> (count == ($past(count) + 4'd1))
    );

endmodule