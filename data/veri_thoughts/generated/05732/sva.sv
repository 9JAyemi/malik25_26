module counter_sva #
(
    parameter integer WIDTH = 4
)
(
    input logic                 clk,
    input logic                 rst,
    input logic                 en,
    input logic [WIDTH-1:0]     count
);

    localparam [WIDTH-1:0] MAX_COUNT = {WIDTH{1'b1}};

    // Synchronous reset clears count on the following clock.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == '0)
    );

    // When disabled, count holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (rst) !en |=> (count == $past(count))
    );

    // When enabled below max, count increments by one.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (rst) en && (count != MAX_COUNT) |=> (count == ($past(count) + 1'b1))
    );

    // When enabled at max, count wraps back to zero.
    check_count_wraps_at_max: assert property (
        @(posedge clk) disable iff (rst) en && (count == MAX_COUNT) |=> (count == '0)
    );

    // Reset takes priority even when enable is high.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) rst && en |=> (count == '0)
    );

    // Any enabled cycle causes the count to change.
    check_count_changes_when_enabled: assert property (
        @(posedge clk) disable iff (rst) en |=> (count != $past(count))
    );

endmodule