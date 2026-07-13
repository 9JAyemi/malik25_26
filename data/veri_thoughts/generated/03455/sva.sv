module binary_counter_sva #(
    parameter [3:0] start_value = 4'd4
) (
    input logic       clk,
    input logic       cen,
    input logic       dir,
    input logic       rst,
    input logic [3:0] out
);

    // Synchronous reset overrides counting and loads start_value.
    check_reset_load_start_value: assert property (
        @(posedge clk) rst |=> (out == start_value)
    );

    // When count enable is low, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        (!cen) |=> (out == $past(out))
    );

    // When enabled with dir low, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (rst)
        (cen && (dir == 1'b0)) |=> (out == ($past(out) + 4'd1))
    );

    // When enabled with dir high, the counter decrements by one.
    check_decrement_when_enabled: assert property (
        @(posedge clk) disable iff (rst)
        (cen && (dir == 1'b1)) |=> (out == ($past(out) - 4'd1))
    );

endmodule