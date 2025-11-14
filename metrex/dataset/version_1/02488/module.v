


module spi2(

	clock, sck,   sdo,   sdi,   bsync, start, rdy,   speed, din,  dout  );

	input clock;


	output sck;
	wire   sck;

	output sdo;

	input sdi;

	output reg bsync;

	input start;

	output rdy;


	input [1:0] speed;

	input [7:0] din;

	output reg [7:0] dout;



	reg [4:0] counter; wire enable_n; reg [6:0] shiftin; reg [7:0] shiftout; wire ena_shout_load; wire g_ena;
	reg [2:0] wcnt;


	initial begin
		counter = 5'b10000;
		shiftout = 8'd0;
		shiftout = 7'd0;
		bsync = 1'd0;
		dout = 1'b0;
	end


	assign rdy = enable_n;

	assign sck = counter[0];

	assign enable_n = counter[4];

	assign sdo = shiftout[7];

	assign ena_shout_load = (start | sck) & g_ena;




	always @(posedge clock)
	begin
		if( g_ena )
		begin
			if( start )
			begin
				counter <= 5'b00000; bsync <= 1'b1; end
			else
			begin
				if( !sck ) begin
      	                  shiftin[6:0] <= { shiftin[5:0], sdi };

					if( (&counter[3:1]) && (!enable_n) )
						dout <= { shiftin[6:0], sdi }; end
				else begin
					bsync <= 1'b0;
				end

				if( !enable_n )
					counter <= counter + 5'd1;
			end
		end
	end


	always @(posedge clock)
	begin
		if( ena_shout_load )
		begin
			if( start )
				shiftout <= din;
			else shiftout[7:0] <= { shiftout[6:0], shiftout[0] }; end
	end


	always @(posedge clock)
	begin
		if( speed!=2'b00 )
		begin
			if( start )
				wcnt <= 3'b001;
			else if( enable_n )
				wcnt <= 3'b000;
			else
				wcnt <= wcnt + 3'd1;
		end
		else
			wcnt <= 3'b000;
	end

	assign g_ena = (speed==2'b00) ? 1'b1 :
	               (speed==2'b01) ? (wcnt[0]  == 1'b0   ) :
	               (speed==2'b10) ? (wcnt[1:0]== 2'b00  ) :
	                                (wcnt[2:0]== 3'b000 ) ;


endmodule

