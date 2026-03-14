
module alt_ctl(op,func,aluc
    );
	input [5:0] op,func;
	output reg [4:0] aluc;
	always @* 
	begin
		case(op)
			6'b001000 : begin
				case(func)
					6'b100000 : aluc =  0;	6'b100010 : aluc =  1;	6'b100100 : aluc =  2;	6'b100101 : aluc =  3;	6'b100110 : aluc =  4;	6'b101010 : aluc =  5;	6'b000000 : aluc =  6;	6'b000100 : aluc =  7;	6'b000011 : aluc =  8;	6'b000111 : aluc =  9;	6'b000010 : aluc = 10;	6'b000110 : aluc = 11;	6'b000001 : aluc = 12;	6'b000010 : aluc = 13;	6'b011011 : aluc = 14; default   : aluc =  0;
				endcase
			end
			6'b000000 : aluc =  0;
			6'b000001 : aluc =  1;
			6'b000010 : aluc =  2;
			6'b000011 : aluc =  3;
			6'b000100 : aluc =  5;
			6'b000101 : aluc = 14;
			6'b001001 : aluc =  1;
			6'b001010 : aluc =  13;default : aluc = 0;
		endcase
	end
	
endmodule
