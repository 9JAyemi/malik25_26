
module Sprite_Controller # ( parameter SizeX= 32, parameter SizeY=32) (

	input wire [9:0] iColumnCount,
	input wire[9:0] iRowCount,
   input wire imask,
	input wire iEnable,
	input wire [9:0] iPosX,
	input wire [9:0] iPosY,
	input wire [2:0] iColorSprite,
	input wire [2:0] iColorBack ,
	output reg [2:0] oRGB
	
	);

	
	always @ (*)
		begin 
			if(iColumnCount <= SizeX + iPosX && iRowCount <= SizeY + iPosY  
			&& iColumnCount >= iPosX && iRowCount >= iPosY && iEnable == 1 && imask == 1 ) 
				begin
					 oRGB <= iColorSprite;
				end 
			else 
				begin 
					oRGB <= iColorBack;
				end	
		end  
endmodule
