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

// Clear 2'b10 or 2'b11 forces pos_diff_x to zero.
    check_pos_diff_x_zero_on_clear: assert property (
        @(posedge clk) (clear == 2'b10 || clear == 2'b11) |-> (pos_diff_x == 16'h0000)
    );

// Clear 2'b10 or 2'b11 forces pos_diff_y to zero.
    check_pos_diff_y_zero_on_clear: assert property (
        @(posedge clk) (clear == 2'b10 || clear == 2'b11) |-> (pos_diff_y == 16'h0000)
    );

// Clear 2'b10 or 2'b11 forces count_clk to zero.
    check_count_clk_zero_on_clear: assert property (
        @(posedge clk) (clear == 2'b10 || clear == 2'b11) |-> (count_clk == 32'h0000_0000)
    );

// Clear 2'b01, 2'b10, or 2'b11 updates prev_pos11 from pos11.
    check_prev_pos11_update_on_clear: assert property (
        @(posedge clk) (clear[1] || clear[0]) |-> (prev_pos11 == $past(pos11))
    );

// Clear 2'b01, 2'b10, or 2'b11 updates prev_pos12 from pos12.
    check_prev_pos12_update_on_clear: assert property (
        @(posedge clk) (clear[1] || clear[0]) |-> (prev_pos12 == $past(pos12))
    );

// Clear 2'b01, 2'b10, or 2'b11 updates prev_pos21 from pos21.
    check_prev_pos21_update_on_clear: assert property (
        @(posedge clk) (clear[1] || clear[0]) |-> (prev_pos21 == $past(pos21))
    );

// Clear 2'b01, 2'b10, or 2'b11 updates prev_pos22 from pos22.
    check_prev_pos22_update_on_clear: assert property (
        @(posedge clk) (clear[1] || clear[0]) |-> (prev_pos22 == $past(pos22))
    );

// Clear 2'b00 leaves prev_pos11 unchanged.
    check_prev_pos11_hold_when_no_clear: assert property (
        @(posedge clk) !clear[1] && !clear[0] |-> (prev_pos11 == $past(prev_pos11))
    );

// Clear 2'b00 leaves prev_pos12 unchanged.
    check_prev_pos12_hold_when_no_clear: assert property (
        @(posedge clk) !clear[1] && !clear[0] |-> (prev_pos12 == $past(prev_pos12))
    );

// Clear 2'b00 leaves prev_pos21 unchanged.
    check_prev_pos21_hold_when_no_clear: assert property (
        @(posedge clk) !clear[1] && !clear[0] |-> (prev_pos21 == $past(prev_pos21))
    );

// Clear 2'b00 leaves prev_pos22 unchanged.
    check_prev_pos22_hold_when_no_clear: assert property (
        @(posedge clk) !clear[1] && !clear[0] |-> (prev_pos22 == $past(prev_pos22))
    );

// Clear 2'b00 increments count_clk by one.
    check_count_clk_increment_when_no_clear: assert property (
        @(posedge clk) !clear[1] && !clear[0] |-> (count_clk == $past(count_clk) + 32'd1)
    );

endmodule
