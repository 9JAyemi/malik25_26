module reset_stretch_sva #(
    parameter int N = 4
)(
    input  logic             clk,
    input  logic             rst_in,
    input  logic             rst_out,
    // Internal signals from DUT (use hierarchical bind to connect)
    input  logic             reset_reg,
    input  logic [N-1:0]     count_reg
);
    // Clock: clk (posedge). Reset: rst_in (active-high, asynchronous). Logic: sequential counter with async reset and stretched deassert.

    // rst_out must mirror internal reset_reg.
    check_rst_out_mapping: assert property (
        @(posedge clk) rst_out == reset_reg
    );

    // When rst_in is asserted, next cycle count_reg is 0 and rst_out is 1.
    check_async_reset_values_next: assert property (
        @(posedge clk) rst_in |=> (count_reg == '0) && (rst_out == 1'b1)
    );

    // If rst_in stays asserted across cycles, count_reg remains 0 and rst_out remains 1.
    check_hold_while_reset: assert property (
        @(posedge clk) (rst_in && $past(rst_in)) |-> (count_reg == '0) && (rst_out == 1'b1)
    );

    // When not in reset and not saturated, count increments by 1 on the next cycle.
    check_count_increment_until_saturated: assert property (
        @(posedge clk) disable iff (rst_in) (!(&count_reg)) |=> (count_reg == $past(count_reg) + 1'b1)
    );

    // When not in reset and not saturated, rst_out is 1 on the next cycle.
    check_out_high_until_saturated: assert property (
        @(posedge clk) disable iff (rst_in) (!(&count_reg)) |=> (rst_out == 1'b1)
    );

    // When not in reset and saturated, rst_out is 0 on the next cycle.
    check_out_low_when_saturated: assert property (
        @(posedge clk) disable iff (rst_in) (&count_reg) |=> (rst_out == 1'b0)
    );

    // When saturated (and not in reset), count_reg holds its value.
    check_count_stable_when_saturated: assert property (
        @(posedge clk) disable iff (rst_in) (&count_reg) |=> (count_reg == $past(count_reg))
    );

    // In normal operation, low rst_out implies counter is saturated.
    check_out_low_implies_saturated: assert property (
        @(posedge clk) disable iff (rst_in) (rst_out == 1'b0) |-> (&count_reg)
    );

    // In normal operation, high rst_out implies counter is not saturated.
    check_out_high_implies_not_saturated: assert property (
        @(posedge clk) disable iff (rst_in) (rst_out == 1'b1) |-> (!(&count_reg))
    );

    // On the first cycle that saturation occurs, rst_out falls.
    check_fall_on_saturation_edge: assert property (
        @(posedge clk) disable iff (rst_in) (!$past(&count_reg) && &count_reg) |-> $fell(rst_out)
    );

endmodule