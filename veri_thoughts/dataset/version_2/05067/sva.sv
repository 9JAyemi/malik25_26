module counter_module_sva(
    input logic clk,
    input logic rst,
    input logic en,
    input logic [3:0] count
);

    // Reset clears the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'b0000)
    );

    // Reset has priority even when enable is high.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (rst && en) |=> (count == 4'b0000)
    );

    // Counter increments by one when enabled.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (rst)
        en |=> (count == ($past(count) + 4'd1))
    );

    // Counter holds its value when enable is low.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        (!en) |=> (count == $past(count))
    );

    // Counter wraps from 15 back to 0 when enabled.
    check_count_wraps_after_max: assert property (
        @(posedge clk) disable iff (rst)
        (en && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule