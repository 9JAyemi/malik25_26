```systemverilog
module Sprite_Controller_assertions (
    input logic CLK,
    input logic RESETn,
    input logic [9:0] iColumnCount,
    input logic [9:0] iRowCount,
    input logic imask,
    input logic iEnable,
    input logic [9:0] iPosX,
    input logic [9:0] iPosY,
    input logic [2:0] iColorSprite,
    input logic [2:0] iColorBack,
    output logic [2:0] oRGB
);

    // Sequential logic for oRGB
    // oRGB should be updated on the rising edge of the clock
    sequential_update: assert property (
        @(posedge CLK) disable iff (!RESETn) oRGB == (iColumnCount <= SizeX + iPosX && iRowCount <= SizeY + iPosY && iColumnCount >= iPosX && iRowCount >= iPosY && iEnable == 1 && imask == 1) ? iColorSprite : iColorBack
    );

    // Reset behavior
    // At reset, oRGB should be driven to iColorBack
    reset_behavior: assert property (
        @(posedge CLK) !RESETn |-> oRGB == iColorBack
    );

    // Enable and mask behavior
    // oRGB should only be updated when iEnable is 1 and imask is 1
    enable_mask_behavior: assert property (
        @(posedge CLK) disable iff (!RESETn) (oRGB == iColorSprite) |-> (iEnable == 1 && imask == 1)
    );

    // Column and row bounds check
    // oRGB should only be updated when iColumnCount and iRowCount are within bounds
    bounds_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (oRGB == iColorSprite) |-> (iColumnCount <= SizeX + iPosX && iRowCount <= SizeY + iPosY && iColumnCount >= iPosX && iRowCount >= iPosY)
    );

endmodule
```