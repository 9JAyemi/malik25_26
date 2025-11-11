


module jt12_sh #(parameter width=5, stages=24 )
(
	input 				clk,
	input				clk_en ,
	input	[width-1:0]	din,
   	output	[width-1:0]	drop
);

reg [stages-1:0] bits[width-1:0];

genvar i;
generate
	for (i=0; i < width; i=i+1) begin: bit_shifter
		always @(posedge clk) if(clk_en) begin
			bits[i] <= {bits[i][stages-2:0], din[i]};
		end
		assign drop[i] = bits[i][stages-1];
	end
endgenerate

endmodule
