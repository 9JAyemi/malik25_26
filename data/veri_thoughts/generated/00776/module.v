module write_axi_9bit(
		 input clock_recovery,
		 input clock_50,
		 input reset_n,
		 input [8:0] data_rec,
		 output reg [8:0] data_stand	
		);


always@(posedge clock_50 or negedge reset_n )
begin

	if(!reset_n)
	begin
		data_stand <= 9'd0;
	end
	else
	begin
		if(clock_recovery)
			data_stand <= data_rec;
		else
			data_stand <= data_stand;
	end
end

endmodule
