

module ff_d #(parameter WIDTH=8) (
		input wire		[WIDTH - 1 : 0]	D,		
		input wire						en,		
		input wire						clk,	
		input wire						res,	
		output wire		[WIDTH - 1 : 0]	Q		
    );
	
	reg [WIDTH - 1 : 0] storage;
	assign Q = storage;
	
	always @(posedge clk) begin
		if(res)									
			storage <= {WIDTH{1'b0}};
		else if(en)								
			storage <= D;
	end
endmodule

