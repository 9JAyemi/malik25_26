module Sprite_Controller_sva (
    input logic clk,
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

// oRGB must match the RTL's full conditional expression.
    check_full_condition: assert property (
        @(posedge clk)
        oRGB == ( (iColumnCount <= (SizeX + iPosX)) &&
                  (iRowCount <= (SizeY + iPosY)) &&
                  (iColumnCount >= iPosX) &&
                  (iRowCount >= iPosY) &&
                  (iEnable == 1'b1) &&
                  (imask == 1'b1) )
                  ? iColorSprite
                  : iColorBack
    );

// When the full condition is true, oRGB selects iColorSprite.
    check_select_sprite: assert property (
        @(posedge clk)
        ( (iColumnCount <= (SizeX + iPosX)) &&
          (iRowCount <= (SizeY + iPosY)) &&
          (iColumnCount >= iPosX) &&
          (iRowCount >= iPosY) &&
          (iEnable == 1'b1) &&
          (imask == 1'b1) )
        |-> (oRGB == iColorSprite)
    );

// When the full condition is false, oRGB selects iColorBack.
    check_select_background: assert property (
        @(posedge clk)
        !( (iColumnCount <= (SizeX + iPosX)) &&
           (iRowCount <= (SizeY + iPosY)) &&
           (iColumnCount >= iPosX) &&
           (iRowCount >= iPosY) &&
           (iEnable == 1'b1) &&
           (imask == 1'b1) )
        |-> (oRGB == iColorBack)
    );

// A disabled display forces oRGB to iColorBack.
    check_disabled_forces_background: assert property (
        @(posedge clk)
        (iEnable == 1'b0) |-> (oRGB == iColorBack)
    );

// A masked display forces oRGB to iColorBack.
    check_masked_forces_background: assert property (
        @(posedge clk)
        (imask == 1'b0) |-> (oRGB == iColorBack)
    );

// A display outside the sprite area forces oRGB to iColorBack.
    check_out_of_area_forces_background: assert property (
        @(posedge clk)
        ( (iColumnCount > (SizeX + iPosX)) ||
          (iRowCount > (SizeY + iPosY)) ||
          (iColumnCount < iPosX) ||
          (iRowCount < iPosY) )
        |-> (oRGB == iColorBack)
    );

endmodule
