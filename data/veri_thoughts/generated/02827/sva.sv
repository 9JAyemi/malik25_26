module clockdivide2_sva (
    input logic clk,
    input logic rst,
    input logic select,
    input logic [31:0] OUT1,
    input logic [31:0] OUT2,
    input logic clkdivided1hz,
    input logic clkdivided2hz,
    input logic clkselect
);
    // When reset is asserted, both counters are driven to 0.
    reset_counters_zero: assert property (
        @(posedge clk) rst |-> (OUT1 == 32'd0) && (OUT2 == 32'd0)
    );

    // On reset deassertion edge, counters are 0 in that cycle.
    reset_fall_counters_zero: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (OUT1 == 32'd0) && (OUT2 == 32'd0)
    );

    // OUT1 never exceeds its terminal count when not in reset.
    out1_within_range: assert property (
        @(posedge clk) disable iff (rst) OUT1 <= 32'd50000000
    );

    // OUT2 never exceeds its terminal count when not in reset.
    out2_within_range: assert property (
        @(posedge clk) disable iff (rst) OUT2 <= 32'd500000
    );

    // OUT1 wraps to 0 on the cycle after reaching 50,000,000.
    out1_wraps_to_zero: assert property (
        @(posedge clk) disable iff (rst) (OUT1 == 32'd50000000) |=> (OUT1 == 32'd0)
    );

    // OUT2 wraps to 0 on the cycle after reaching 500,000.
    out2_wraps_to_zero: assert property (
        @(posedge clk) disable iff (rst) (OUT2 == 32'd500000) |=> (OUT2 == 32'd0)
    );

    // clkdivided1hz reflects OUT1 == 50,000,000.
    clkdiv1_definition: assert property (
        @(posedge clk) disable iff (rst) clkdivided1hz == (OUT1 == 32'd50000000)
    );

    // clkdivided2hz reflects OUT2 == 500,000.
    clkdiv2_definition: assert property (
        @(posedge clk) disable iff (rst) clkdivided2hz == (OUT2 == 32'd500000)
    );

    // clkdivided1hz is a single-cycle pulse (cannot be high in two consecutive cycles).
    clkdiv1_one_cycle_pulse: assert property (
        @(posedge clk) disable iff (rst) clkdivided1hz |=> !clkdivided1hz
    );

    // clkdivided2hz is a single-cycle pulse (cannot be high in two consecutive cycles).
    clkdiv2_one_cycle_pulse: assert property (
        @(posedge clk) disable iff (rst) clkdivided2hz |=> !clkdivided2hz
    );

    // clkselect is the mux of the two divided clocks based on select.
    clkselect_mux_behavior: assert property (
        @(posedge clk) disable iff (rst) clkselect == (select ? clkdivided2hz : clkdivided1hz)
    );
endmodule