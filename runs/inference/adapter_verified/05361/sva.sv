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

// Reset drives all outputs to zero.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |-> (r == 8'h00) && (g == 8'h00) && (b == 8'h00)
    );

// Outside active video, all outputs are zero.
    check_idle_outputs_zero: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1 || vsync == 1) |-> (r == 8'h00) && (g == 8'h00) && (b == 8'h00)
    );

// Inside active video, all outputs are equal.
    check_active_video_outputs_equal: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 0 && vsync == 0) |-> (r == g) && (g == b)
    );

// Inside active video, the common output value is within the 0..63 range.
    check_active_video_common_value_range: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 0 && vsync == 0) |-> (r <= 8'd63)
    );

// Inside active video, the common output value matches the horizontal count LSBs.
    check_active_video_common_value_matches_hcount_lsb: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 0 && vsync == 0) |-> (r == h_count[5:0])
    );

// Inside active video, the common output value matches the vertical count LSBs.
    check_active_video_common_value_matches_vcount_lsb: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 0 && vsync == 0) |-> (r == v_count[5:0])
    );

// Horizontal sync high forces all outputs to zero.
    check_hsync_forces_zero: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1) |-> (r == 8'h00) && (g == 8'h00) && (b == 8'h00)
    );

// Vertical sync high forces all outputs to zero.
    check_vsync_forces_zero: assert property (
        @(posedge clk) disable iff (rst)
        (vsync == 1) |-> (r == 8'h00) && (g == 8'h00) && (b == 8'h00)
    );

endmodule
