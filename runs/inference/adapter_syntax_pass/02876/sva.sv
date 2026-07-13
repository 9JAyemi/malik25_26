module Sprite_Controller_sva #(
    parameter int SizeX = 32,
    parameter int SizeY = 32
) (
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

    // oRGB must match the RTL's combinational selection function.
    check_output_matches_rtl_function: assert property (
        @($global_clock)
        oRGB == ( (iColumnCount <= (SizeX + iPosX)) &&
                  (iRowCount <= (SizeY + iPosY)) &&
                  (iColumnCount >= iPosX) &&
                  (iRowCount >= iPosY) &&
                  (iEnable == 1'b1) &&
                  (imask == 1'b1) )
                  ? iColorSprite
                  : iColorBack
    );

    // When the sprite is enabled and within bounds, oRGB selects the sprite color.
    check_sprite_selected_when_enabled_and_in_bounds: assert property (
        @($global_clock)
        ( (iColumnCount <= (SizeX + iPosX)) &&
          (iRowCount <= (SizeY + iPosY)) &&
          (iColumnCount >= iPosX) &&
          (iRowCount >= iPosY) &&
          (iEnable == 1'b1) &&
          (imask == 1'b1) )
        |-> (oRGB == iColorSprite)
    );

    // When the sprite is disabled, oRGB selects the background color.
    check_background_selected_when_disabled: assert property (
        @($global_clock)
        (iEnable == 1'b0) |-> (oRGB == iColorBack)
    );

    // When the sprite is masked, oRGB selects the background color.
    check_background_selected_when_masked: assert property (
        @($global_clock)
        (imask == 1'b0) |-> (oRGB == iColorBack)
    );

    // When the sprite is outside the visible area, oRGB selects the background color.
    check_background_selected_when_out_of_bounds: assert property (
        @($global_clock)
        ( (iColumnCount > (SizeX + iPosX)) ||
          (iRowCount > (SizeY + iPosY)) ||
          (iColumnCount < iPosX) ||
          (iRowCount < iPosY) )
        |-> (oRGB == iColorBack)
    );

    // oRGB can never be the sprite color when the sprite is disabled.
    check_sprite_color_impossible_when_disabled: assert property (
        @($global_clock)
        (iEnable == 1'b0) |-> (oRGB != iColorSprite)
    );

    // oRGB can never be the sprite color when the sprite is masked.
    check_sprite_color_impossible_when_masked: assert property (
        @($global_clock)
        (imask == 1'b0) |-> (oRGB != iColorSprite)
    );

    // oRGB can never be the sprite color when the sprite is outside the visible area.
    check_sprite_color_impossible_when_out_of_bounds: assert property (
        @($global_clock)
        ( (iColumnCount > (SizeX + iPosX)) ||
          (iRowCount > (SizeY + iPosY)) ||
          (iColumnCount < iPosX) ||
          (iRowCount < iPosY) )
        |-> (oRGB != iColorSprite)
    );

endmodule