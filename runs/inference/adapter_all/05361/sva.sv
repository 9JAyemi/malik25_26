module vga_color_generator_sva (
    input logic clk,
    input logic rst,
    input logic [9:0] x,
    input logic [9:0] y,
    input logic hsync,
    input logic vsync,
    input logic [7:0] r,
    input logic [7:0] g,
    input logic [7:0] b
);

    // Reset drives all outputs low.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |-> (r == 8'h00) && (g == 8'h00) && (b == 8'h00)
    );

    // Outside active video, all outputs are low.
    check_idle_outputs_low: assert property (
        @(posedge clk) disable iff (rst)
        (hsync || vsync) |-> (r == 8'h00) && (g == 8'h00) && (b == 8'h00)
    );

    // In active video, all outputs match.
    check_active_outputs_match: assert property (
        @(posedge clk) disable iff (rst)
        (!hsync && !vsync) |-> (r == g) && (g == b)
    );

    // In active video, the common output value is the low byte of x.
    check_active_output_matches_x: assert property (
        @(posedge clk) disable iff (rst)
        (!hsync && !vsync) |-> (r == x[7:0])
    );

    // In active video, the common output value is the low byte of y.
    check_active_output_matches_y: assert property (
        @(posedge clk) disable iff (rst)
        (!hsync && !vsync) |-> (r == y[7:0])
    );

    // In active video, the common output value is the low byte of x or y.
    check_active_output_matches_xy: assert property (
        @(posedge clk) disable iff (rst)
        (!hsync && !vsync) |-> (r == x[7:0]) || (r == y[7:0])
    );

    // In active video, the common output value is always 8 bits wide.
    check_active_output_width: assert property (
        @(posedge clk) disable iff (rst)
        (!hsync && !vsync) |-> (r[7:0] == x[7:0])
    );

    // In active video, the common output value is always 8 bits wide.
    check_active_output_width: assert property (
        @(posedge clk) disable iff (rst)
        (!hsync && !vsync) |-> (g[7:0] == x[7:0])
    );

    // In active video, the common output value is always 8 bits wide.
    check_active_output_width: assert property (
        @(posedge clk) disable iff (rst)
        (!hsync && !vsync) |-> (b[7:0] == x[7:0])
    );

endmodule