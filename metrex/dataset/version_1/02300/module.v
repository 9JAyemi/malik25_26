
module sram (
	clock,
	data,
	rdaddress,
	wraddress,
	wren,
	q);

	input	  clock;
	input	[15:0]  data;
	input	[11:0]  rdaddress;
	input	[11:0]  wraddress;
	input	  wren;
	output reg [15:0]  q;

	reg [15:0] mem [0:(1<<12)-1];

	always @(posedge clock) begin
		if (wren) begin
			mem[wraddress] <= data;
		end else begin
			q <= mem[rdaddress];
		end
	end

endmodule
