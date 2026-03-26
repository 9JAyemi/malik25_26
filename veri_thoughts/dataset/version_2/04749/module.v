
module output_module(
	input  ctrl1_zone,
	input  ctrl2_zone,
	input  statusb_zone,
	input  [9:0] p1_in,
	input  [9:0] p2_in,
	input  nwp,
	input  ncd2,
	input  ncd1,
	input  system_mode,
	output reg [7:0] m68k_data
);

	always @(*) begin
		if (ctrl1_zone) begin
			m68k_data = 8'b00000000;
		end
		else if (ctrl2_zone) begin
			m68k_data = 8'b00000000;
		end
		else if (statusb_zone) begin
			m68k_data = {system_mode, nwp, ncd2, ncd1, p2_in[9:8], p1_in[9:8]};
		end
		else begin
			m68k_data = p1_in[7:0];
		end
	end

endmodule