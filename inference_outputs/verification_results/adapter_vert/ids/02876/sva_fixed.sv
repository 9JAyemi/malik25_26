module Sprite_Controller_sva (
    input logic iColorSprite,
    input logic iColumnCount,
    input logic iEnable,
    input logic iPosX,
    input logic iPosY,
    input logic iRowCount,
    input logic imask,
    input logic oRGB,
    input logic SizeX,
    input logic SizeY,
    input logic clk_in_14
);

property ValidDataeotid; @(posedge clk_in_14) (iColumnCount) <= (SizeX + iPosX) && (iRowCount) <= (SizeY + iPosY) &&  (iColumnCount) >= (iPosX) &&  (iRowCount) >= (iPosY) &&  (iEnable) == 1 &&  (imask) == 1 |-> (oRGB) == (iColorSprite) ;endproperty
assert property (ValidDataeotid);

property ValidRuneotid; @(posedge clk_in_14) (iColumnCount) <= (SizeX + iPosX) && (iRowCount) <= (SizeY + iPosY) &&  (iColumnCount) >= (iPosX) &&  (iRowCount) >= (iPosY) &&  (iEnable) == 1 &&  (imask) == 1 |-> (oRGB) == (iColorSprite) ;endproperty
assert property (ValidRuneotid);

property ValidRuneotid_2; @(posedge clk_in_14) (iColumnCount) <= (SizeX + iPosX) && (iRowCount) <= (SizeY + iPosY) &&  (iColumnCount) >= (iPosX) &&  (iRowCount) >= (iPosY) &&  (iEnable) == 1 &&  (imask) == 1 |-> (oRGB) == (iColorSprite) ;endproperty
assert property (ValidRuneotid_2);

property ValidRuneotid_3; @(posedge clk_in_14) (iColumnCount) <= (SizeX + iPosX) && (iRowCount) <= (SizeY + iPosY) &&  (iColumnCount) >= (iPosX) &&  (iRowCount) >= (iPosY) &&  (iEnable) == 1 &&  (imask) == 1 |-> (oRGB) == (iColorSprite) ;endproperty
assert property (ValidRuneotid_3);

endmodule