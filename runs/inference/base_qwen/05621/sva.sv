module ClockDividerAssertions (
    input logic clk,
    input logic rst,
    input logic [31:0] Divisor,
    input logic clkOut,
    input logic [31:0] count
);
    // Reset behavior: At reset, count and clkOut should be 0
    reset: assert property (
        @(posedge clk) disable iff (!rst) (rst |-> (count == 32'b0) && (clkOut == 1'b0))
    );

    // Count behavior: Count should increment until it reaches the divisor, then reset to 0
    count_increment: assert property (
        @(posedge clk) disable iff (!rst) (count_i != Divisor - 1 |-> count_i + 1 == count_i)
    );

    // ClockOut behavior: clkOut should toggle when count reaches the divisor minus one
    clock_out_toggle: assert property (
        @(posedge clk) disable iff (!rst) (count_i == Divisor - 1 |-> clkOut_i != clkOut)
    );

    // Count should not exceed the divisor
    count_limit: assert property (
        @(posedge clk) disable iff (!rst) (count_i <= Divisor)
    );

    // clkOut should be 0 when count is not at the divisor minus one
    clock_out_zero: assert property (
        @(posedge clk) disable iff (!rst) (count_i != Divisor - 1 |-> clkOut == 1'b0)
    );

    // Count should not be negative
    count_non_negative: assert property (
        @(posedge clk) disable iff (!rst) (count_i >= 32'b0)
    );

    // clkOut should be 1 when count is at the divisor minus one
    clock_out_one: assert property (
        @(posedge clk) disable iff (!rst) (count_i == Divisor - 1 |-> clkOut == 1'b1)
    );

    // Count should not wrap around unexpectedly
    count_wraparound: assert property (
        @(posedge clk) disable iff (!rst) (count_i != Divisor - 1 |-> count_i + 1 != count_i)
    );

    // clkOut should not toggle unexpectedly
    clock_out_toggle_unexpected: assert property (
        @(posedge clk) disable iff (!rst) (count_i != Divisor - 1 |-> clkOut_i == clkOut)
    );

    // Count should not exceed the maximum value
    count_max_value: assert property (
        @(posedge clk) disable iff (!rst) (count_i <= 32'hFFFFFFFF)
    );
endmodule