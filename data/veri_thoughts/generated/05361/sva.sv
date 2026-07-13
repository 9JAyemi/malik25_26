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

    // State and RGB are cleared on the first clock after reset is released.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (rst)
        $past(rst) |-> (h_count == 10'h0 && v_count == 10'h0 &&
                        r == 8'h00 && g == 8'h00 && b == 8'h00)
    );

    // h_count increments when hsync is low and the line has not wrapped.
    check_hcount_increment: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1'b0 && h_count != 10'd799) |=> (h_count == $past(h_count) + 10'd1)
    );

    // h_count wraps to zero at the end of the line.
    check_hcount_wrap_to_zero: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1'b0 && h_count == 10'd799) |=> (h_count == 10'h0)
    );

    // h_count holds when hsync is high.
    check_hcount_hold_when_hsync_high: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1'b1) |=> (h_count == $past(h_count))
    );

    // v_count increments on a line wrap when vsync is low and the frame has not wrapped.
    check_vcount_increment: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1'b0 && h_count == 10'd799 && vsync == 1'b0 && v_count != 10'd524)
        |=> (v_count == $past(v_count) + 10'd1)
    );

    // v_count wraps to zero at the end of the frame.
    check_vcount_wrap_to_zero: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1'b0 && h_count == 10'd799 && vsync == 1'b0 && v_count == 10'd524)
        |=> (v_count == 10'h0)
    );

    // v_count holds whenever the vertical update condition is not met.
    check_vcount_hold_without_frame_tick: assert property (
        @(posedge clk) disable iff (rst)
        !(hsync == 1'b0 && h_count == 10'd799 && vsync == 1'b0)
        |=> (v_count == $past(v_count))
    );

    // color is zero in the blanking border region.
    check_color_blank_border: assert property (
        @(posedge clk) disable iff (rst)
        ((h_count < 10'd8) || (h_count >= 10'd792) || (v_count < 10'd8) || (v_count >= 10'd488))
        |-> (color == 8'h00)
    );

    // color matches the low-range active-area expression.
    check_color_low_range: assert property (
        @(posedge clk) disable iff (rst)
        (h_count >= 10'd8 && h_count < 10'd648 && v_count >= 10'd8 && v_count < 10'd488)
        |-> (color == {2'b00, h_count[5:0]})
    );

    // color matches the high-range active-area expression.
    check_color_high_range: assert property (
        @(posedge clk) disable iff (rst)
        (h_count >= 10'd648 && h_count < 10'd792 && v_count >= 10'd8 && v_count < 10'd488)
        |-> (color == (8'hff - (h_count[5:0] - 8'h08)))
    );

    // RGB outputs load color when both syncs are low.
    check_rgb_loads_color: assert property (
        @(posedge clk) disable iff (rst)
        (hsync == 1'b0 && vsync == 1'b0)
        |=> (r == $past(color) && g == $past(color) && b == $past(color))
    );

    // RGB outputs are forced to zero when either sync is high.
    check_rgb_zero_when_sync_not_both_low: assert property (
        @(posedge clk) disable iff (rst)
        !(hsync == 1'b0 && vsync == 1'b0)
        |=> (r == 8'h00 && g == 8'h00 && b == 8'h00)
    );

endmodule