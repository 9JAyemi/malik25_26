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
    check_count_clk_clears_on_10_or_11: assert property (
        @(posedge clk) (clear == 2'b10 || clear == 2'b11) |=> (count_clk == 32'd0)
    );

    // Clear 2'b01, 2'b10, or 2'b11 causes the position registers to capture pos11/pos12.
    check_position_registers_capture_on_01_10_11: assert property (
        @(posedge clk) (clear == 2'b01 || clear == 2'b10 || clear == 2'b11) |=> (
            $stable($past(pos11)) && $stable($past(pos12)) &&
            (pos11 == $past(pos11)) && (pos12 == $past(pos12))
        )
    );

    // Clear 2'b00 causes the position registers to update based on m1/m2.
    check_position_registers_update_on_00: assert property (
        @(posedge clk) (clear == 2'b00) |=> (
            $stable($past(pos11)) && $stable($past(pos12)) &&
            $stable($past(pos21)) && $stable($past(pos22)) &&
            (pos11 == ($past(pos11) + ($past(m1) ? 16'd1 : 16'd-1))) &&
            (pos12 == ($past(pos12) + ($past(m1) ? 16'd1 : 16'd-1))) &&
            (pos21 == ($past(pos21) + ($past(m2) ? 16'd1 : 16'd-1))) &&
            (pos22 == ($past(pos22) + ($past(m2) ? 16'd1 : 16'd-1)))
        )
    );

    // Clear 2'b00 with m1 high increments pos11 and pos12.
    check_position_registers_increment_on_m1: assert property (
        @(posedge clk) (clear == 2'b00 && m1 == 1'b1) |=> (
            $stable($past(pos11)) && $stable($past(pos12)) &&
            (pos11 == ($past(pos11) + 16'd1)) &&
            (pos12 == ($past(pos12) + 16'd1))
        )
    );

    // Clear 2'b00 with m1 low decrements pos11 and pos12.
    check_position_registers_decrement_on_m1: assert property (
        @(posedge clk) (clear == 2'b00 && m1 == 1'b0) |=> (
            $stable($past(pos11)) && $stable($past(pos12)) &&
            (pos11 == ($past(pos11) - 16'd1)) &&
            (pos12 == ($past(pos12) - 16'd1))
        )
    );

    // Clear 2'b00 with m2 high increments pos21 and pos22.
    check_position_registers_increment_on_m2: assert property (
        @(posedge clk) (clear == 2'b00 && m2 == 1'b1) |=> (
            $stable($past(pos21)) && $stable($past(pos22)) &&
            (pos21 == ($past(pos21) + 16'd1)) &&
            (pos22 == ($past(pos22) + 16'd1))
        )
    );

    // Clear 2'b00 with m2 low decrements pos21 and pos22.
    check_position_registers_decrement_on_m2: assert property (
        @(posedge clk) (clear == 2'b00 && m2 == 1'b0) |=> (
            $stable($past(pos21)) && $stable($past(pos22)) &&
            (pos21 == ($past(pos21) - 16'd1)) &&
            (pos22 == ($past(pos22) - 16'd1))
        )
    );

    // Clear 2'b10 or 2'b11 forces pos_diff_x to zero on the next cycle.
    check_pos_diff_x_clears_on_10_or_11: assert property (
        @(posedge clk) (clear == 2'b10 || clear == 2'b11) |=> (pos_diff_x == 16'd0)
    );

    // Clear 2'b10 or 2'b11 forces pos_diff_y to zero on the next cycle.
    check_pos_diff_y_clears_on_10_or_11: assert property (
        @(posedge clk) (clear == 2'b10 || clear == 2'b11) |=> (pos_diff_y == 16'd0)
    );

    // Clear 2'b00 causes pos_diff_x to reflect pos11 - pos21.
    check_pos_diff_x_update_on_00: assert property (
        @(posedge clk) (clear == 2'b00) |=> (pos_diff_x == (pos11 - pos21))
    );

    // Clear 2'b00 causes pos_diff_y to reflect pos12 - pos22.
    check_pos_diff_y_update_on_00: assert property (
        @(posedge clk) (clear == 2'b00) |=> (pos_diff_y == (pos12 - pos22))
    );

endmodule