module Sprite_Controller_sva #(
    parameter int SizeX = 32,
    parameter int SizeY = 32
)(
    input logic [9:0] iColumnCount,
    input logic [9:0] iRowCount,
    input logic       imask,
    input logic       iEnable,
    input logic [9:0] iPosX,
    input logic [9:0] iPosY,
    input logic [2:0] iColorSprite,
    input logic [2:0] iColorBack,
    input logic [2:0] oRGB
);

    // No clock/reset in RTL; combinational logic. Sample assertions on posedge of iEnable.

    // When inside box with enable/mask high, drive sprite color.
    sprite_when_inside_and_enabled: assert property (
        @(posedge iEnable)
        (imask == 1'b1) && (iEnable == 1'b1) &&
        (iColumnCount <= (SizeX + iPosX)) && (iColumnCount >= iPosX) &&
        (iRowCount    <= (SizeY + iPosY)) && (iRowCount    >= iPosY)
        |-> (oRGB == iColorSprite)
    );

    // If mask is low, drive background color.
    background_when_mask_low: assert property (
        @(posedge iEnable)
        (imask == 1'b0) |-> (oRGB == iColorBack)
    );

    // If enable is low, drive background color.
    background_when_enable_low: assert property (
        @(posedge iEnable)
        (iEnable == 1'b0) |-> (oRGB == iColorBack)
    );

    // If column is left of sprite region, drive background color.
    background_when_left_of_box: assert property (
        @(posedge iEnable)
        (iColumnCount < iPosX) |-> (oRGB == iColorBack)
    );

    // If row is above sprite region, drive background color.
    background_when_above_box: assert property (
        @(posedge iEnable)
        (iRowCount < iPosY) |-> (oRGB == iColorBack)
    );

    // If column is right of sprite region, drive background color.
    background_when_right_of_box: assert property (
        @(posedge iEnable)
        (iColumnCount > (SizeX + iPosX)) |-> (oRGB == iColorBack)
    );

    // If row is below sprite region, drive background color.
    background_when_below_box: assert property (
        @(posedge iEnable)
        (iRowCount > (SizeY + iPosY)) |-> (oRGB == iColorBack)
    );

    // Output is always either sprite color or background color.
    output_is_sprite_or_background_only: assert property (
        @(posedge iEnable)
        (oRGB == iColorSprite) || (oRGB == iColorBack)
    );

    // Left edge inclusive: at left boundary with other coords in range and enables high, sprite color.
    sprite_on_left_edge: assert property (
        @(posedge iEnable)
        (imask == 1'b1) && (iEnable == 1'b1) &&
        (iColumnCount == iPosX) &&
        (iRowCount    >= iPosY) && (iRowCount <= (SizeY + iPosY)) &&
        (iColumnCount <= (SizeX + iPosX))
        |-> (oRGB == iColorSprite)
    );

    // Right edge inclusive: at right boundary with other coords in range and enables high, sprite color.
    sprite_on_right_edge: assert property (
        @(posedge iEnable)
        (imask == 1'b1) && (iEnable == 1'b1) &&
        (iColumnCount == (SizeX + iPosX)) &&
        (iRowCount    >= iPosY) && (iRowCount <= (SizeY + iPosY)) &&
        (iColumnCount >= iPosX)
        |-> (oRGB == iColorSprite)
    );

    // Top edge inclusive: at top boundary with other coords in range and enables high, sprite color.
    sprite_on_top_edge: assert property (
        @(posedge iEnable)
        (imask == 1'b1) && (iEnable == 1'b1) &&
        (iRowCount == iPosY) &&
        (iColumnCount >= iPosX) && (iColumnCount <= (SizeX + iPosX)) &&
        (iRowCount   <= (SizeY + iPosY))
        |-> (oRGB == iColorSprite)
    );

    // Bottom edge inclusive: at bottom boundary with other coords in range and enables high, sprite color.
    sprite_on_bottom_edge: assert property (
        @(posedge iEnable)
        (imask == 1'b1) && (iEnable == 1'b1) &&
        (iRowCount == (SizeY + iPosY)) &&
        (iColumnCount >= iPosX) && (iColumnCount <= (SizeX + iPosX)) &&
        (iRowCount   >= iPosY)
        |-> (oRGB == iColorSprite)
    );

endmodule