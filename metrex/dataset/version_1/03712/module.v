module LUT # (parameter SIZE=8)
(
 input wire [SIZE-1:0] A,
 input wire [1:0] B,
 output reg [SIZE+1:0] Result
);

wire [SIZE+1:0] wD0, wD1, wD2, wD3;

assign wD1 = {2'b0, A};
assign wD0 = wD1 ^ wD1; // Esto siempre es cero, de la longitud adecuada.
assign wD2 = {1'b0, A, 1'b0}; 
assign wD3 = {2'b0, A, 2'b0};

always @ (A, B)
begin
	case (B)
	//-------------------------------------	
	2'b00:
	begin
		Result <= wD0;
	end
	//-------------------------------------	
	2'b01:
	begin
		Result <= wD1;
	end
	//-------------------------------------	
	2'b10:
	begin
		Result <= wD2;
	end
	//-------------------------------------	
	2'b11:
	begin
		Result <= wD3;
	end
	//-------------------------------------	
	endcase
end

endmodule