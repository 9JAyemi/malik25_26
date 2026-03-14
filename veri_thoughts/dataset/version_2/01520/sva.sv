module hvsync_generator_sva (
    input logic clk,
    input logic vga_h_sync,
    input logic vga_v_sync,
    input logic inDisplayArea,
    input logic [10:0] CounterX,
    input logic [10:0] CounterY
);
    // Clock: clk; no reset in RTL. Sequential counters and sync regs; inDisplayArea is combinational.

    localparam int unsigned WIDTH        = 800;
    localparam int unsigned HEIGHT       = 600;
    localparam int unsigned COUNT_DOTS   = 1056;
    localparam int unsigned COUNT_LINES  = 625;
    localparam int unsigned H_FRONT      = 16;
    localparam int unsigned H_SYNC       = 80;
    localparam int unsigned V_FRONT      = 1;
    localparam int unsigned V_SYNC       = 3;

    // CounterX increments by 1 when not at COUNT_DOTS.
    check_counterX_increments: assert property (
        @(posedge clk) (CounterX != COUNT_DOTS) |=> (CounterX == $past(CounterX) + 11'd1)
    );

    // CounterX wraps to 0 when equal to COUNT_DOTS.
    check_counterX_wrap: assert property (
        @(posedge clk) (CounterX == COUNT_DOTS) |=> (CounterX == 11'd0)
    );

    // CounterY holds when CounterX is not COUNT_DOTS.
    check_counterY_hold_when_X_not_max: assert property (
        @(posedge clk) (CounterX != COUNT_DOTS) |=> (CounterY == $past(CounterY))
    );

    // CounterY increments by 1 when CounterX is COUNT_DOTS and CounterY not COUNT_LINES.
    check_counterY_increment_on_Xmax: assert property (
        @(posedge clk) (CounterX == COUNT_DOTS && CounterY != COUNT_LINES) |=> (CounterY == $past(CounterY) + 11'd1)
    );

    // CounterY wraps to 0 when both counters are at their maxima.
    check_counterY_wrap_on_both_max: assert property (
        @(posedge clk) (CounterX == COUNT_DOTS && CounterY == COUNT_LINES) |=> (CounterY == 11'd0)
    );

    // CounterY changes only when previous CounterX was COUNT_DOTS.
    check_counterY_changes_only_on_prev_Xmax: assert property (
        @(posedge clk) (CounterY != $past(CounterY)) |-> ($past(CounterX) == COUNT_DOTS)
    );

    // vga_h_sync equals registered HS expression of CounterX.
    check_vga_h_sync_definition: assert property (
        @(posedge clk) vga_h_sync == (($past(CounterX) >= (WIDTH + H_FRONT)) && ($past(CounterX) < (WIDTH + H_FRONT + H_SYNC)))
    );

    // vga_v_sync equals registered VS expression of CounterY.
    check_vga_v_sync_definition: assert property (
        @(posedge clk) vga_v_sync == (($past(CounterY) >= (HEIGHT + V_FRONT)) && ($past(CounterY) < (HEIGHT + V_FRONT + V_SYNC)))
    );

    // inDisplayArea is 1 only when CounterX < WIDTH and CounterY < HEIGHT.
    check_inDisplayArea_definition: assert property (
        @(posedge clk) inDisplayArea == ((CounterX < WIDTH) && (CounterY < HEIGHT))
    );

    // vga_h_sync is LOW when $past(CounterX) is outside the HS window.
    check_vga_h_sync_low_outside_window: assert property (
        @(posedge clk)
            (($past(CounterX) < (WIDTH + H_FRONT)) || ($past(CounterX) >= (WIDTH + H_FRONT + H_SYNC))) |-> (vga_h_sync == 1'b0)
    );

    // vga_v_sync is LOW when $past(CounterY) is outside the VS window.
    check_vga_v_sync_low_outside_window: assert property (
        @(posedge clk)
            (($past(CounterY) < (HEIGHT + V_FRONT)) || ($past(CounterY) >= (HEIGHT + V_FRONT + V_SYNC))) |-> (vga_v_sync == 1'b0)
    );
endmodule