module tone_lut32 (input [5:0] tone, output [15:0] thirty_second_period);
	
	parameter
				C3  = 16'd23890,
				C3S = 16'd22549,
				D3  = 16'd21283,
				D3S = 16'd20089,
				E3  = 16'd18961,
				F3  = 16'd17897,
				F3S = 16'd16892,
				G3  = 16'd15944,
				G3S = 16'd15050,
				A3  = 16'd14205,
				A3S = 16'd13408,
				B3  = 16'd12655,
				
				C4  = 16'd11945,
				C4S = 16'd11275,
				D4  = 16'd10642,
				D4S = 16'd10044,
				E4  = 16'd9481,
				F4  = 16'd8949,
				F4S = 16'd8446,
				G4  = 16'd7972,
				G4S = 16'd7525,
				A4  = 16'd7103,
				A4S = 16'd6704,
				B4  = 16'd6328,
				
				C5  = 16'd5973,
				C5S = 16'd5637,
				D5  = 16'd5321,
				D5S = 16'd5022,
				E5  = 16'd4740,
				F5  = 16'd4474,
				F5S = 16'd4223,
				G5  = 16'd3986,
				G5S = 16'd3763,
				A5  = 16'd3551,
				A5S = 16'd3352,
				B5  = 16'd3164,
				
				C6  = 16'd2986,
				C6S = 16'd2819,
				D6  = 16'd2661,
				D6S = 16'd2511,
				E6  = 16'd2370,
				F6  = 16'd2237,
				F6S = 16'd2112,
				G6  = 16'd1993,
				G6S = 16'd1881,
				A6  = 16'd1776,
				A6S = 16'd1676,
				B6  = 16'd1582;
				
	assign thirty_second_period =
										 
									   (tone == 6'd1)  ? C3  :
									   (tone == 6'd2)  ? C3S :
									   (tone == 6'd3)  ? D3  :
										(tone == 6'd4)  ? D3S :
										(tone == 6'd5)  ? E3  :
										(tone == 6'd6)  ? F3  :
										(tone == 6'd7)  ? F3S :
										(tone == 6'd8)  ? G3  :
										(tone == 6'd9)  ? G3S :
										(tone == 6'd10)  ? A3  :
										(tone == 6'd11) ? A3S :
										(tone == 6'd12) ? B3  :
									
										(tone == 6'd13) ? C4  :
										(tone == 6'd14) ? C4S :
										(tone == 6'd15) ? D4  :
										(tone == 6'd16) ? D4S :
										(tone == 6'd17) ? E4  :
										(tone == 6'd18) ? F4  :
										(tone == 6'd19) ? F4S :
										(tone == 6'd20) ? G4  :
										(tone == 6'd21) ? G4S :
										(tone == 6'd22) ? A4  :
										(tone == 6'd23) ? A4S :
										(tone == 6'd24) ? B4  :
									
										(tone == 6'd25) ? C5  :
										(tone == 6'd26) ? C5S :
										(tone == 6'd27) ? D5  :
										(tone == 6'd28) ? D5S :
										(tone == 6'd29) ? E5  :
										(tone == 6'd30) ? F5  :
										(tone == 6'd31) ? F5S :
										(tone == 6'd32) ? G5  :
										(tone == 6'd33) ? G5S :
										(tone == 6'd34) ? A5  :
										(tone == 6'd35) ? A5S :
										(tone == 6'd36) ? B5  :
									 
										(tone == 6'd37) ? C6  :
										(tone == 6'd38) ? C6S :
										(tone == 6'd39) ? D6  :
										(tone == 6'd40) ? D6S :
										(tone == 6'd41) ? E6  :
										(tone == 6'd42) ? F6  :
										(tone == 6'd43) ? F6S :
										(tone == 6'd44) ? G6  :
										(tone == 6'd45) ? G6S :
										(tone == 6'd46) ? A6  :
										(tone == 6'd47) ? A6S :
										(tone == 6'd48) ? B6  :
										  0 ;

endmodule
