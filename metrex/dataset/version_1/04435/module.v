
module shift_register(input clk, stb, di, output reg do);
	localparam integer DIN_N = 256;
	localparam integer DOUT_N = 256;

	reg [DIN_N-1:0] din;
	reg [DIN_N-1:0] din_shr;
	reg [DOUT_N-1:0] dout;
	reg [DOUT_N-1:0] dout_shr;

	always @(posedge clk) begin
		din_shr <= {din_shr, di};
		dout_shr <= {dout_shr, din_shr[DIN_N-1]};
		if (stb) begin
			din <= din_shr;
			dout <= dout_shr;
		end
	end

	always @(posedge clk) begin
		do <= dout_shr[DOUT_N-1];  // Corrected the assignment of do to dout_shr[DOUT_N-1]
	end

endmodule
