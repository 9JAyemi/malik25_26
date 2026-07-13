module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [2:0] count
);

    // Active-low reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst |-> (count == 3'b000)
    );

    // The first sampled cycle after reset release still sees zero.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (!rst) $rose(rst) |-> (count == 3'b000)
    );

    // The first active cycle after reset release still sees zero.
    check_first_active_cycle_zero: assert property (
        @(posedge clk) disable iff (!rst) $rose(rst) |=> (count == 3'b000)
    );

    // The first active cycle after reset release then increments to one.
    check_first_active_cycle_one: assert property (
        @(posedge clk) disable iff (!rst) $rose(rst) |=> (count == 3'b001)
    );

    // The counter increments by one on each active clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |=> (count == ($past(count) + 3'b001))
    );

    // The 3-bit counter wraps from 7 back to 0.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (!rst) (count == 3'b111) |=> (count == 3'b000)
    );

endmodule