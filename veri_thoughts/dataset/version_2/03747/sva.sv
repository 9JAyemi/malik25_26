module Apple_sva(
    input logic        clk,
    input logic        rst,
    input logic        signal,
    input logic [7:0]  apple_x,
    input logic [7:0]  apple_y,
    input logic [31:0] clk_cnt,
    input logic [10:0] random_num
);

    // Reset forces the counter and apple position to their default values.
    check_reset_defaults: assert property (
        @(posedge clk) !rst |-> (clk_cnt == 32'd0 && apple_x == 8'd24 && apple_y == 8'd10)
    );

    // After reset release, the apple position stays at the reset location until the first update window.
    check_post_reset_hold: assert property (
        @(posedge clk) $rose(rst) |-> ((apple_x == 8'd24) && (apple_y == 8'd10))[*250001]
    );

    // random_num increments by 999 on each clock.
    check_random_num_increment: assert property (
        @(posedge clk) disable iff (!rst)
        $past(rst) |-> (random_num == ($past(random_num) + 11'd999))
    );

    // clk_cnt increments by one while it is below 250000.
    check_clk_cnt_increment: assert property (
        @(posedge clk) disable iff (!rst)
        $past(rst) && ($past(clk_cnt) != 32'd250000) |-> (clk_cnt == ($past(clk_cnt) + 32'd1))
    );

    // clk_cnt wraps to zero when it reaches 250000.
    check_clk_cnt_wrap: assert property (
        @(posedge clk) disable iff (!rst)
        $past(rst) && ($past(clk_cnt) == 32'd250000) |-> (clk_cnt == 32'd0)
    );

    // apple_x and apple_y hold their values when no update is enabled.
    check_outputs_hold_without_update: assert property (
        @(posedge clk) disable iff (!rst)
        $past(rst) && !(($past(clk_cnt) == 32'd250000) && $past(signal)) |->
            (apple_x == $past(apple_x) && apple_y == $past(apple_y))
    );

    // apple_x follows the coded mapping at an enabled update point.
    check_apple_x_update_formula: assert property (
        @(posedge clk) disable iff (!rst)
        $past(rst) && ($past(clk_cnt) == 32'd250000) && $past(signal) |->
            (apple_x ==
                (($past(random_num[10:5]) > 6'd38) ? ($past(random_num[10:5]) - 6'd25) :
                 (($past(random_num[10:5]) == 6'd0) ? 6'd1 : $past(random_num[10:5]))))
    );

    // apple_y follows the coded mapping at an enabled update point.
    check_apple_y_update_formula: assert property (
        @(posedge clk) disable iff (!rst)
        $past(rst) && ($past(clk_cnt) == 32'd250000) && $past(signal) |->
            (apple_y ==
                (($past(random_num[4:0]) > 5'd28) ? ($past(random_num[4:0]) - 5'd3) :
                 (($past(random_num[4:0]) == 5'd0) ? 5'd1 : $past(random_num[4:0]))))
    );

    // Updated apple positions stay within the RTL's x and y bounds.
    check_updated_position_range: assert property (
        @(posedge clk) disable iff (!rst)
        $past(rst) && ($past(clk_cnt) == 32'd250000) && $past(signal) |->
            (apple_x >= 8'd1 && apple_x <= 8'd38 &&
             apple_y >= 8'd1 && apple_y <= 8'd28)
    );

endmodule