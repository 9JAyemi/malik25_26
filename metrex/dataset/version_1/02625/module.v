module
	timer#(
		parameter
		COUNTER_WIDTH = 25,
		CEILING_WIDTH = 4
	)(
		input  wire                    clk_in,
		input  wire[CEILING_WIDTH-1:0] ceiling_in,
		output reg                     tick_out
	);

	localparam TOP_BIT = 2**CEILING_WIDTH - 1;
	function[TOP_BIT:0] reverse(input[COUNTER_WIDTH:0] fwd);
		integer i;
		for ( i = 0; i <= TOP_BIT; i = i + 1 )
			reverse[i] = fwd[COUNTER_WIDTH-i];
	endfunction
	reg[COUNTER_WIDTH:0] count_next, count = 0;
	wire[TOP_BIT:0] revCount;

	always @(posedge clk_in)
		count <= count_next;

	assign revCount = reverse(count);
	
	always @*
	begin
		if ( revCount[ceiling_in] == 1'b0 )
			begin
				count_next = count + 1'b1;
				tick_out = 1'b0;
			end
		else
			begin
				count_next = 0;
				tick_out = 1'b1;
			end
	end
endmodule
