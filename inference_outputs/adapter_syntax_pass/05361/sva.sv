module vga_color_generator_sva (
    input logic clk,
    input logic rst,
    input logic [9:0] x,
    input logic [9:0] y,
    input logic hsync,
    input logic vsync,
    input logic [7:0] r,
    input logic [7:0] g,
    input logic [7:0] b,
    input logic [9:0] h_count,
    input logic [9:0] v_count,
    input logic [7:0] color
);

    // Reset clears the horizontal counter.
    check_reset_clears_h_count: assert property (
        @(posedge clk) rst |-> (h_count == 10'h000)
    );

    // Reset clears the vertical counter.
    check_reset_clears_v_count: assert property (
        @(posedge clk) rst |-> (v_count == 10'h000)
    );

    // Reset clears the RGB outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |-> ((r == 8'h00) && (g == 8'h00) && (b == 8'h00))
    );

    // Horizontal count increments on active video.
    check_h_count_increments: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1'b0 && h_count != 10'h30F) |=> (h_count == ($past(h_count) + 10'd1))
    );

    // Horizontal count wraps to zero at the end of active video.
    check_h_count_wraps: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1'b0 && h_count == 10'h30F) |=> (h_count == 10'h000)
    );

    // Vertical count increments on the next line after the active region.
    check_v_count_increments: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1'b0 && h_count == 10'h30F && v_count != 10'h20C) |=> (v_count == ($past(v_count) + 10'd1))
    );

    // Vertical count wraps to zero at the end of active video.
    check_v_count_wraps: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1'b0 && h_count == 10'h30F && v_count == 10'h20C) |=> (v_count == 10'h000)
    );

    // Color is zero outside the active display region.
    check_color_zero_outside_active: assert property (
        @(posedge clk) disable iff (rst)
        ((h_count < 10'd8) || (h_count >= 10'd792) || (v_count < 10'd8) || (v_count >= 10'd488)) |-> (color == 8'h00)
    );

    // Color is the horizontal count value within the active display region.
    check_color_matches_horizontal_count: assert property (
        @(posedge clk) disable iff (rst)
        ((h_count >= 10'd8) && (h_count < 10'd648) && (v_count >= 10'd8) && (v_count < 10'd488)) |-> (color == {8'h00, h_count[5:0]})
    );

    // Color is the inverted horizontal count value above the active region.
    check_color_matches_inverted_horizontal_count: assert property (
        @(posedge clk) disable iff (rst)
        ((h_count >= 10'd648) && (h_count < 10'd792) && (v_count >= 10'd8) && (v_count < 10'd488)) |-> (color == {8'h00, 8'hFF - (h_count[5:0] - 6'd8)})
    );

    // RGB outputs are zero when hsync or vsync is high.
    check_outputs_zero_when_sync_active: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1'b1 || vsync == 1'b1) |-> ((r == 8'h00) && (g == 8'h00) && (b == 8'h00))
    );

    // RGB outputs mirror the color value when both syncs are low.
    check_outputs_mirror_color: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1'b0 && vsync == 1'b0) |-> ((r == color) && (g == color) && (b == color))
    );

endmodule