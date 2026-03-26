
module loadable_downcounter8 ( countClock, count, loadvalue, load, countout);

	input wire countClock;
	input wire count;
	input wire [7:0] loadvalue;
	input wire load;
	 output reg [7:0] countout;

		always@(posedge countClock) 
		begin

			if (load == 1'b1) countout <= loadvalue;
			else countout <= countout - count;

		end
	
endmodule
