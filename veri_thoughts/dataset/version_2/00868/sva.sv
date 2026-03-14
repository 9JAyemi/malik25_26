module Key_sva (
    input  logic        clk,
    input  logic        rst,
    input  logic        left,
    input  logic        right,
    input  logic        up,
    input  logic        down,
    input  logic [7:0]  direction,
    input  logic [31:0] clk_cnt,
    input  logic        left_key_last,
    input  logic        right_key_last,
    input  logic        up_key_last,
    input  logic        down_key_last
);
    ///// Reset behavior /////
    // While rst is LOW, all registers/outputs must be 0.
    reset_values: assert property (
        @(posedge clk) !rst |-> (clk_cnt == 32'd0) && (direction == 8'b0000_0000) &&
                         (left_key_last == 1'b0) && (right_key_last == 1'b0) &&
                         (up_key_last == 1'b0) && (down_key_last == 1'b0)
    );

    ///// Counter behavior /////
    // When not at limit, clk_cnt increments by 1 on the next cycle.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (!rst) (clk_cnt != 32'd50000) |=> (clk_cnt == $past(clk_cnt) + 32'd1)
    );
    // When at limit, clk_cnt wraps to 0 on the next cycle.
    check_counter_wraps: assert property (
        @(posedge clk) disable iff (!rst) (clk_cnt == 32'd50000) |=> (clk_cnt == 32'd0)
    );

    ///// Key last-value capture at sample /////
    // At sample, left_key_last captures current left on next cycle.
    capture_left_last: assert property (
        @(posedge clk) disable iff (!rst) (clk_cnt == 32'd50000) |=> (left_key_last == $past(left))
    );
    // At sample, right_key_last captures current right on next cycle.
    capture_right_last: assert property (
        @(posedge clk) disable iff (!rst) (clk_cnt == 32'd50000) |=> (right_key_last == $past(right))
    );
    // At sample, up_key_last captures current up on next cycle.
    capture_up_last: assert property (
        @(posedge clk) disable iff (!rst) (clk_cnt == 32'd50000) |=> (up_key_last == $past(up))
    );
    // At sample, down_key_last captures current down on next cycle.
    capture_down_last: assert property (
        @(posedge clk) disable iff (!rst) (clk_cnt == 32'd50000) |=> (down_key_last == $past(down))
    );

    ///// Direction encoding and timing /////
    // direction only takes values 0,1,2,3,4.
    check_direction_encoding: assert property (
        @(posedge clk) disable iff (!rst) direction inside {
            8'b0000_0000, 8'b0000_0001, 8'b0000_0010, 8'b0000_0011, 8'b0000_0100
        }
    );
    // A non-zero direction is a one-cycle pulse (next cycle observed as zero).
    direction_one_cycle_pulse: assert property (
        @(posedge clk) disable iff (!rst) (direction != 8'b0000_0000) |=> (direction == 8'b0000_0000)
    );
    // Non-zero direction implies previous cycle was a sample with at least one rising key.
    direction_implies_prior_edge: assert property (
        @(posedge clk) disable iff (!rst)
            (direction != 8'b0000_0000) |->
            ($past(clk_cnt) == 32'd50000) &&
            (
                (($past(left_key_last)  == 1'b0) && ($past(left)  == 1'b1)) ||
                (($past(right_key_last) == 1'b0) && ($past(right) == 1'b1)) ||
                (($past(up_key_last)    == 1'b0) && ($past(up)    == 1'b1)) ||
                (($past(down_key_last)  == 1'b0) && ($past(down)  == 1'b1))
            )
    );

    ///// Direction priority on simultaneous edges (down > up > right > left) /////
    // If down rises at sample, next observed direction is 4.
    dir_on_down_rise: assert property (
        @(posedge clk) disable iff (!rst)
            (clk_cnt == 32'd50000) && (down_key_last == 1'b0) && (down == 1'b1)
            |=> (direction == 8'b0000_0100)
    );
    // If up rises (and down does not) at sample, next observed direction is 3.
    dir_on_up_rise_no_down: assert property (
        @(posedge clk) disable iff (!rst)
            (clk_cnt == 32'd50000) &&
            (up_key_last == 1'b0) && (up == 1'b1) &&
            !((down_key_last == 1'b0) && (down == 1'b1))
            |=> (direction == 8'b0000_0011)
    );
    // If right rises (and up/down do not) at sample, next observed direction is 2.
    dir_on_right_rise_no_up_down: assert property (
        @(posedge clk) disable iff (!rst)
            (clk_cnt == 32'd50000) &&
            (right_key_last == 1'b0) && (right == 1'b1) &&
            !((up_key_last == 1'b0) && (up == 1'b1)) &&
            !((down_key_last == 1'b0) && (down == 1'b1))
            |=> (direction == 8'b0000_0010)
    );
    // If left rises (and right/up/down do not) at sample, next observed direction is 1.
    dir_on_left_rise_no_others: assert property (
        @(posedge clk) disable iff (!rst)
            (clk_cnt == 32'd50000) &&
            (left_key_last == 1'b0) && (left == 1'b1) &&
            !((right_key_last == 1'b0) && (right == 1'b1)) &&
            !((up_key_last == 1'b0) && (up == 1'b1)) &&
            !((down_key_last == 1'b0) && (down == 1'b1))
            |=> (direction == 8'b0000_0001)
    );
endmodule