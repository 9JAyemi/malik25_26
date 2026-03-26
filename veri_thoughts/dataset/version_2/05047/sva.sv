module vga_split_controller_assertions (
    input logic [15:0] rgb_0,
    input logic [15:0] rgb_1,
    input logic        clock,
    input logic        hsync,
    input logic [15:0] rgb
);

    // When hsync is high, the truncated concatenation captured into rgb equals rgb_1.
    check_capture_on_hsync: assert property (
        @(posedge clock) hsync |=> (rgb == $past(rgb_1))
    );

    // When hsync is low, rgb holds its previous value.
    check_hold_when_hsync_low: assert property (
        @(posedge clock) !hsync |=> (rgb == $past(rgb))
    );

    // When hsync is high, rgb upper byte is taken from rgb_1 upper byte.
    check_capture_upper_byte_on_hsync: assert property (
        @(posedge clock) hsync |=> (rgb[15:8] == $past(rgb_1[15:8]))
    );

    // When hsync is high, rgb lower byte is taken from rgb_1 lower byte.
    check_capture_lower_byte_on_hsync: assert property (
        @(posedge clock) hsync |=> (rgb[7:0] == $past(rgb_1[7:0]))
    );

endmodule