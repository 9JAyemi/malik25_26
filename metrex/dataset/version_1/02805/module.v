



module jt51_lfo_lfsr #(parameter init=220 )(
	input	rst,
	input	clk,
	input	base,
	output	out
);

reg [18:0] bb;
assign out = bb[18];

reg last_base;

always @(posedge clk) begin : base_counter
	if( rst ) begin
		bb			<= init[18:0];
		last_base 	<= 1'b0;
	end
	else begin
		last_base <= base;
		if( last_base != base ) begin	
			bb[18:1] 	<= bb[17:0];
			bb[0]		<= ^{bb[0],bb[1],bb[14],bb[15],bb[17],bb[18]};
		end
	end
end

endmodule
