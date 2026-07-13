module ClockDivider_assertions (
    input logic clk,
    input logic rst,
    input logic [31:0] Divisor,
    input logic clkOut
);
    // Reset behavior: At reset, clkOut should be LOW.
    reset: assert property (
        @(posedge clk) disable iff (!rst) clkOut == 1'b0
    );

    // Clock division behavior: clkOut toggles every Divisor clock cycles.
    clock_division: assert property (
        @(posedge clk) disable iff (!rst) |-> (clkOut_i == clkOut)
    );

    // Count register behavior: count_i increments until it reaches Divisor - 1.
    count_increment: assert property (
        @(posedge clk) disable iff (!rst) |-> (count_i == Divisor - 1)
    );

    // Count reset behavior: count_i is reset to 0 on reset.
    count_reset: assert property (
        @(posedge clk) disable iff (!rst) |-> (count_i == 0)
    );

    // ClockOut toggle behavior: clkOut toggles on every Divisor clock cycles.
    clock_out_toggle: assert property (
        @(posedge clk) disable iff (!rst) |-> (clkOut_i == !clkOut_i)
    );

    // Count overflow behavior: count_i overflows back to 0 after reaching Divisor - 1.
    count_overflow: assert property (
        @(posedge clk) disable iff (!rst) |-> (count_i == 0)
    );

    // ClockOut reset behavior: clkOut is reset to 0 on reset.
    clock_out_reset: assert property (
        @(posedge clk) disable iff (!rst) |-> (clkOut_i == 0)
    );

    // Clock division behavior: clkOut toggles every Divisor clock cycles.
    clock_division_2: assert property (
        @(posedge clk) disable iff (!rst) |-> (clkOut_i == clkOut)
    );

    // Count register behavior: count_i increments until it reaches Divisor - 1.
    count_increment_2: assert property (
        @(posedge clk) disable iff (!rst) |-> (count_i == Divisor - 1)
    );

    // Count reset behavior: count_i is reset to 0 on reset.
    count_reset_2: assert property (
        @(posedge clk) disable iff (!rst) |-> (count_i == 0)
    );

    // ClockOut toggle behavior: clkOut toggles on every Divisor clock cycles.
    clock_out_toggle_2: assert property (
        @(posedge clk) disable iff (!rst) |-> (clkOut_i == !clkOut_i)
    );

    // Count overflow behavior: count_i overflows back to 0 after reaching Divisor - 1.
    count_overflow_2: assert property (
        @(posedge clk) disable iff (!rst) |-> (count_i == 0)
    );

    // ClockOut reset behavior: clkOut is reset to 0 on reset.
    clock_out_reset_2: assert property (
        @(posedge clk) disable iff (!rst) |-> (clkOut_i == 0)
    );
endmodule