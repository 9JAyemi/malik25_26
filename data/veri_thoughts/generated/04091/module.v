module erosion_sys_cycle_time
	(
		input 		clock,
		input 		resetn,
		output [31:0] 		cur_cycle
	);

	reg [31:0] cur_count_NO_SHIFT_REG;

	assign cur_cycle = cur_count_NO_SHIFT_REG;

	always @(posedge clock or negedge resetn)
	begin
		if (~(resetn))
		begin
			cur_count_NO_SHIFT_REG <= 32'h0;
		end
		else
		begin
			cur_count_NO_SHIFT_REG <= (cur_count_NO_SHIFT_REG + 32'h1);
		end
	end

endmodule