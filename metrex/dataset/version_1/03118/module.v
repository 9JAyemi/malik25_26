module dma_access(

	input            clk,

	input            rst_n,


	input            dma_req,  input     [21:0] dma_addr, input            dma_rnw,  input      [7:0] dma_wd,   output reg [7:0] dma_rd,   output reg       dma_busynready, output reg       dma_ack, output reg       dma_end, output wire        mem_dma_bus,  output wire [21:0] mem_dma_addr, output wire  [7:0] mem_dma_wd,   input        [7:0] mem_dma_rd,   output wire        mem_dma_rnw,  output reg         mem_dma_oe,   output reg         mem_dma_we,   output reg       busrq_n, input            busak_n  );

	reg dma_bus;

	reg [21:0] int_dma_addr;
	reg        int_dma_rnw;
	reg  [7:0] int_dma_wd;
	wire [7:0] int_dma_rd;

	assign mem_dma_bus  = dma_bus;
	assign mem_dma_addr = int_dma_addr;
	assign mem_dma_wd   = int_dma_wd;
	assign mem_dma_rnw  = int_dma_rnw;
	assign int_dma_rd   = mem_dma_rd;



	localparam IDLE     = 0;
	localparam START    = 1;
	localparam WACK     = 2;
	localparam READ1    = 3;
	localparam READ2    = 4;
	localparam WRITE1   = 5;
	localparam WRITE2   = 6;


	reg [3:0] state;
	reg [3:0] next_state;




	initial
	begin
		state       <= IDLE;
		busrq_n     <= 1'b1;
		mem_dma_oe  <= 1'b1;
		mem_dma_we  <= 1'b1;
	end


always @(posedge clk, negedge rst_n)
	begin
		if( !rst_n )
			state <= IDLE;
		else
			state <= next_state;
	end


	always @*
	begin
		case( state )
IDLE:
		begin
			if( dma_req==1'b1 )
				next_state <= START;
			else
				next_state <= IDLE;
		end
START:
		begin
			next_state <= WACK;
		end
WACK:
		begin
			if( busak_n == 1'b1 ) next_state <= WACK;
			else begin
				if( int_dma_rnw == 1'b1 ) next_state <= READ1;
				else next_state <= WRITE1;
			end
		end
READ1:
		begin
			next_state <= READ2;
		end
READ2:
		begin
			if( dma_req == 1'b0 )
				next_state <= IDLE;
			else begin
				if( dma_rnw == 1'b1 ) next_state <= READ1;
				else next_state <= WRITE1;
			end
		end
WRITE1:
		begin
			next_state <= WRITE2;
		end
WRITE2:
		begin
			if( dma_req == 1'b0 )
				next_state <= IDLE;
			else begin
				if( dma_rnw == 1'b1 ) next_state <= READ1;
				else next_state <= WRITE1;
			end
		end
endcase
	end


	always @(posedge clk, negedge rst_n)
	begin
		if( !rst_n )
		begin
			busrq_n        <= 1'b1;
			dma_busynready <= 1'b0;
			dma_ack        <= 1'b0;
			dma_end        <= 1'b0;
			dma_bus        <= 1'b0;
			mem_dma_oe     <= 1'b1;
		end
		else case( next_state )
IDLE:
		begin
			dma_end        <= 1'b0;

			busrq_n        <= 1'b1;
			dma_bus        <= 1'b0;
			mem_dma_oe     <= 1'b1;
		end
START:
		begin
busrq_n        <= 1'b0;

			dma_busynready <= 1'b1;
			dma_ack        <= 1'b1;

			int_dma_rnw    <= dma_rnw;
			int_dma_addr   <= dma_addr;
			int_dma_wd     <= dma_wd;
		end
WACK:
		begin
			dma_ack <= 1'b0;
		end
READ1:
		begin
			dma_bus    <= 1'b1; mem_dma_oe <= 1'b0;
			if( dma_busynready == 1'b0 ) begin
				dma_busynready <= 1'b1;
				dma_ack        <= 1'b1;
				dma_end        <= 1'b0;
				int_dma_rnw    <= 1'b1;
				int_dma_addr   <= dma_addr;
			end
		end
READ2:
		begin
			dma_busynready <= 1'b0;
			dma_ack        <= 1'b0;
			dma_end        <= 1'b1;
			dma_rd <= int_dma_rd;
		end
WRITE1:
		begin
			dma_bus    <= 1'b1; mem_dma_oe <= 1'b1;

			if( dma_busynready == 1'b0 ) begin
				dma_busynready <= 1'b1;
				dma_ack        <= 1'b1;
				dma_end        <= 1'b0;
				int_dma_rnw    <= 1'b0;
				int_dma_addr   <= dma_addr;
				int_dma_wd     <= dma_wd;
			end
		end
WRITE2:
		begin
			dma_busynready <= 1'b0;
			dma_ack        <= 1'b0;
			dma_end        <= 1'b1;
		end
endcase
	end




always @(negedge clk,negedge rst_n)
	begin
		if( !rst_n )
			mem_dma_we <= 1'b1;
		else
		begin
			if( dma_bus )
			begin
				if( !int_dma_rnw )
					mem_dma_we <= ~mem_dma_we;
			end
			else
				mem_dma_we <= 1'b1;
		end
	end


endmodule

