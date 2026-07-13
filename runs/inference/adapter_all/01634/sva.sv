module posManager_sva (
    input logic        clk,
    input logic [15:0] pos11,
    input logic [15:0] pos12,
    input logic [15:0] pos21,
    input logic [15:0] pos22,
    input logic [15:0] pos_diff_x,
    input logic [15:0] pos_diff_y,
    input logic [31:0] count_clk,
    input logic [1:0]  clear,
    input logic [0:0]  m1,
    input logic [0:0]  m2
);

    // Clear 2'b10 or 2'b11 forces count_clk to zero on the next cycle.
    check_count_clear_value: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b10 || clear == 2'b11) |=> (count_clk == 32'd0)
    );

    // Clear 2'b01, 2'b10, or 2'b11 updates prev_pos11 from pos11 on the next cycle.
    check_pos11_update_clears: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b01 || clear == 2'b10 || clear == 2'b11) |=> (prev_pos11 == $past(pos11))
    );

    // Clear 2'b01, 2'b10, or 2'b11 updates prev_pos12 from pos12 on the next cycle.
    check_pos12_update_clears: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b01 || clear == 2'b10 || clear == 2'b11) |=> (prev_pos12 == $past(pos12))
    );

    // Clear 2'b01, 2'b10, or 2'b11 updates prev_pos21 from pos21 on the next cycle.
    check_pos21_update_clears: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b01 || clear == 2'b10 || clear == 2'b11) |=> (prev_pos21 == $past(pos21))
    );

    // Clear 2'b01, 2'b10, or 2'b11 updates prev_pos22 from pos22 on the next cycle.
    check_pos22_update_clears: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b01 || clear == 2'b10 || clear == 2'b11) |=> (prev_pos22 == $past(pos22))
    );

    // With no clear and m1 low, prev_pos11 decrements on the next cycle.
    check_pos11_decrement_no_m1: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b00 && m1 == 1'b0) |=> (prev_pos11 == ($past(prev_pos11) - 16'd1))
    );

    // With no clear and m1 high, prev_pos11 increments on the next cycle.
    check_pos11_increment_no_m1: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b00 && m1 == 1'b1) |=> (prev_pos11 == ($past(prev_pos11) + 16'd1))
    );

    // With no clear and m2 low, prev_pos21 decrements on the next cycle.
    check_pos21_decrement_no_m2: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b00 && m2 == 1'b0) |=> (prev_pos21 == ($past(prev_pos21) - 16'd1))
    );

    // With no clear and m2 high, prev_pos21 increments on the next cycle.
    check_pos21_increment_no_m2: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b00 && m2 == 1'b1) |=> (prev_pos21 == ($past(prev_pos21) + 16'd1))
    );

    // With no clear, pos_diff_x is the difference of pos11 and pos21.
    check_pos_diff_x_no_clear: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b00) |-> (pos_diff_x == (pos11 - pos21))
    );

    // With no clear, pos_diff_y is the difference of pos12 and pos22.
    check_pos_diff_y_no_clear: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b00) |-> (pos_diff_y == (pos12 - pos22))
    );

    // With clear 2'b10 or 2'b11, pos_diff_x is forced to zero.
    check_pos_diff_x_clear_value: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b10 || clear == 2'b11) |-> (pos_diff_x == 16'd0)
    );

    // With clear 2'b10 or 2'b11, pos_diff_y is forced to zero.
    check_pos_diff_y_clear_value: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b10 || clear == 2'b11) |-> (pos_diff_y == 16'd0)
    );

    // With clear 2'b10 or 2'b11, count_clk is forced to zero.
    check_count_clk_clear_value: assert property (
        @(posedge clk) disable iff (1'b0)
        (clear == 2'b10 || clear == 2'b11) |-> (count_clk == 32'd0)
    );

endmodule