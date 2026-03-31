module Sprite_Controller_sva #(
    parameter int SizeX = 32,
    parameter int SizeY = 32
) (
    input logic [9:0] iColumnCount,
    input logic [9:0] iRowCount,
    input logic imask,
    input logic iEnable,
    input logic [9:0] iPosX,
    input logic [9:0] iPosY,
    input logic [2:0] iColorSprite,
    input logic [2:0] iColorBack,
    input logic [2:0] oRGB
);

    // oRGB must match the selected color based on the implemented conditions.
    check_output_matches_selected_color: assert property (
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

    // When the sprite is enabled and masked, the sprite color must be selected.
    check_sprite_selected_when_enabled: assert property (
        @($global_clock)
        (iEnable && imask) |-> (oRGB == iColorSprite)
    );

    // When the sprite is not enabled, the background color must be selected.
    check_background_selected_when_disabled: assert property (
        @($global_clock)
        (!iEnable) |-> (oRGB == iColorBack)
    );

    // When the sprite is masked, the background color must be selected.
    check_background_selected_when_masked: assert property (
        @($global_clock)
        (!imask) |-> (oRGB == iColorBack)
    );

    // When the sprite is outside the visible area, the background color must be selected.
    check_background_selected_when_out_of_bounds: assert property (
        @($global_clock)
        (iColumnCount > (SizeX + iPosX) ||
         iRowCount > (SizeY + iPosY) ||
         iColumnCount < iPosX ||
         iRowCount < iPosY) |-> (oRGB == iColorBack)
    );

    // If the selected color is unchanged, the output must remain unchanged.
    check_output_stable_when_selected_color_stable: assert property (
        @($global_clock)
        $stable( (iEnable && imask) ? iColorSprite : iColorBack ) |-> $stable(oRGB)
    );

    // If the output changes, the selected color must have changed.
    check_output_change_requires_selected_color_change: assert property (
        @($global_clock)
        $changed(oRGB) |-> $changed( (iEnable && imask) ? iColorSprite : iColorBack )
    );

endmodule