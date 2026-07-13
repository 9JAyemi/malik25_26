module top_sva(
    input logic CLK_24M,
    input logic USR_BTN,
    input logic [2:0] VGA_RGB,
    input logic HSYNC,
    input logic VSYNC,
    input logic enVcnt,
    input logic [10:0] hzcount,
    input logic [10:0] vtcount,
    input logic RED,
    input logic BLU,
    input logic GRN
);

    // Initial state sets the counters and vertical enable low.
    check_initial_state: assert property (
        @(posedge CLK_24M)
        $initstate |-> (enVcnt == 1'b0 && hzcount == 11'd0 && vtcount == 11'd0)
    );

    // Horizontal counter increments and keeps vertical enable low before 799.
    check_hzcount_increment: assert property (
        @(posedge CLK_24M)
        (hzcount < 11'd799) |=> (hzcount == $past(hzcount) + 11'd1 && enVcnt == 1'b0)
    );

    // Horizontal counter wraps and pulses vertical enable at 799 or above.
    check_hzcount_wrap: assert property (
        @(posedge CLK_24M)
        (hzcount >= 11'd799) |=> (hzcount == 11'd0 && enVcnt == 1'b1)
    );

    // Vertical counter holds when the enable pulse is low.
    check_vtcount_hold: assert property (
        @(posedge CLK_24M)
        (!enVcnt) |=> (vtcount == $past(vtcount))
    );

    // Vertical counter increments when enabled and below 524.
    check_vtcount_increment: assert property (
        @(posedge CLK_24M)
        (enVcnt && vtcount < 11'd524) |=> (vtcount == $past(vtcount) + 11'd1)
    );

    // Vertical counter wraps when enabled at 524 or above.
    check_vtcount_wrap: assert property (
        @(posedge CLK_24M)
        (enVcnt && vtcount >= 11'd524) |=> (vtcount == 11'd0)
    );

    // VGA output bus mirrors the internal color registers.
    check_vga_rgb_mapping: assert property (
        @(posedge CLK_24M)
        (VGA_RGB[0] === RED) && (VGA_RGB[1] === GRN) && (VGA_RGB[2] === BLU)
    );

    // HSYNC matches the horizontal sync decode window.
    check_hsync_decode: assert property (
        @(posedge CLK_24M)
        HSYNC == ((hzcount > 11'd655) && (hzcount < 11'd751))
    );

    // VSYNC matches the vertical sync decode window.
    check_vsync_decode: assert property (
        @(posedge CLK_24M)
        VSYNC == ((vtcount > 11'd489) && (vtcount < 11'd491))
    );

    // Outside the active area, all colors are driven low on the next cycle.
    check_blank_rgb_low: assert property (
        @(posedge CLK_24M)
        ((hzcount >= 11'd639) || (vtcount >= 11'd479)) |=> (RED == 1'b0 && GRN == 1'b0 && BLU == 1'b0)
    );

    // Inside the active area, RED updates from the selected vtcount bit.
    check_red_active_update: assert property (
        @(posedge CLK_24M)
        ((hzcount < 11'd639) && (vtcount < 11'd479)) |=> (RED == $past(vtcount[((hzcount >> 6) % 11)]))
    );

endmodule