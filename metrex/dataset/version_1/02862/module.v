
module seven_segment_leds_x_8(
    input [31:0] bcd_in,
    input [7:0] decimal_points,
    input clk,
    output  reg [6:0] a_to_g,
    output reg decimal_point,
    output reg [7:0] anode 
    );

wire [2:0] counter;
reg [3:0] digit;
reg [20:0] clkdiv;	
	 

assign counter = clkdiv[20:18];   always @(posedge clk)
    case(counter)
	0: {digit, decimal_point} = {bcd_in[3:0], ~decimal_points[0]};
	1: {digit, decimal_point} = {bcd_in[7:4], ~decimal_points[1]};
	2: {digit, decimal_point} = {bcd_in[11:8], ~decimal_points[2]};
	3: {digit, decimal_point} = {bcd_in[15:12], ~decimal_points[3]};
	4: {digit, decimal_point} = {bcd_in[19:16], ~decimal_points[4]};
    	5: {digit, decimal_point} = {bcd_in[23:20], ~decimal_points[5]};
    	6: {digit, decimal_point} = {bcd_in[27:24], ~decimal_points[6]};
    	7: {digit, decimal_point} = {bcd_in[31:28], ~decimal_points[7]};
     endcase

always @(posedge clk)
     case(digit)
    	0: a_to_g = 8'b1000000;  1: a_to_g = 8'b1111001;  2: a_to_g = 8'b0100100;  3: a_to_g = 8'b0110000;  4: a_to_g = 8'b0011001;  5: a_to_g = 8'b0010010;  6: a_to_g = 8'b0000010;  7: a_to_g = 8'b1111000;  8: a_to_g = 8'b0000000;  9: a_to_g = 8'b0010000;  default: a_to_g = 8'b11111111;  endcase
	  
always @(posedge clk)
    case(counter)
        0: anode = 8'b11111110;
	1: anode = 8'b11111101;
	2: anode = 8'b11111011;
	3: anode = 8'b11110111;
	4: anode = 8'b11101111;
        5: anode = 8'b11011111;
        6: anode = 8'b10111111;
        7: anode = 8'b01111111;
	default: anode = 8'b11111111;  endcase
     
always  @ (posedge clk)
   begin
	clkdiv <= clkdiv + 21'b1;
    end 
	  
endmodule
