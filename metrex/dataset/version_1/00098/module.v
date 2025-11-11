module LowPassFilter(
	input clk,
	input filter_onoff,
	input signed [15:0] audio_in,
	output signed [15:0] audio_out
);

	wire [15:0] filter_out;
	
	// Instantiate SystolicFilter module
	SystolicFilter SystolicFilter_inst(
		.clk(clk),
		.filter_onoff(filter_onoff),
		.audio_in(audio_in),
		.filter_out(filter_out)
	);

	assign audio_out = filter_onoff ? filter_out : audio_in;

endmodule

module SystolicFilter(
	input clk,
	input filter_onoff,
	input signed [15:0] audio_in,
	output reg [15:0] filter_out
);

	always @(posedge clk) begin
		if (filter_onoff) begin
			// Implement your filter logic here
			filter_out <= audio_in;
		end
	end

endmodule