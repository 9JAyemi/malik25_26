
module SPIinterface(
		txbuffer,
		rxbuffer,
		transmit,
		done_out,
		sdi, sdo,
		rst, clk,
		sclk
);
   
input            clk;
   input            rst;
   input            transmit;
   input            sdi;
	input [15:0]     txbuffer;
   output [7:0]     rxbuffer;
   output           done_out;
   output           sdo;
   output           sclk;
   
   
wire             sclk;
	wire             done_out;
   reg              sdo;
	wire [7:0]		  rxbuffer;
   
   parameter [7:0]  CLKDIVIDER = 8'hFF;		parameter [1:0]  TxType_idle = 0,
                    TxType_transmitting = 1;

   parameter [1:0]  RxType_idle = 0,
                    RxType_recieving = 1;

   parameter [1:0]  SCLKType_idle = 0,
                    SCLKType_running = 1;
						  
   reg [7:0]        clk_count = 7'd0;
   reg              clk_edge_buffer = 1'd0;
   
   reg              sck_previous = 1'b1;
   reg              sck_buffer = 1'b1;
   
   reg [15:0]       tx_shift_register = 16'h0000;
   reg [3:0]        tx_count = 4'h0;
   reg [7:0]        rx_shift_register = 8'h00;
   reg [3:0]        rx_count = 4'h0;

   reg              done = 1'b0;
   reg [1:0]        TxSTATE = TxType_idle;
   reg [1:0]        RxSTATE = RxType_idle;
   reg [1:0]        SCLKSTATE = SCLKType_idle;
   
always @(posedge clk)
		begin: TxProcess
			begin
				if (rst == 1'b1)
				begin
					tx_shift_register <= 16'd0;
					tx_count <= 4'd0;
					sdo <= 1'b1;
					TxSTATE <= TxType_idle;
				end
				else
					case (TxSTATE)
						TxType_idle :
							begin
								tx_shift_register <= txbuffer;
								if (transmit == 1'b1)
									TxSTATE <= TxType_transmitting;
								else if (done == 1'b1)
									sdo <= 1'b1;
							end
						TxType_transmitting :
							if (sck_previous == 1'b1 & sck_buffer == 1'b0)
							begin
								if (tx_count == 4'b1111) begin
									TxSTATE <= TxType_idle;
									tx_count <= 4'd0;
									sdo <= tx_shift_register[15];
								end
								else begin
									tx_count <= tx_count + 4'b0001;
									sdo <= tx_shift_register[15];
									tx_shift_register <= {tx_shift_register[14:0], 1'b0};
								end
							end
					endcase
			end
		end
		
		always @(posedge clk)
		begin: RxProcess
			begin
				if (rst == 1'b1)
				begin
					rx_shift_register <= 8'h00;
					rx_count <= 4'h0;
					done <= 1'b0;
					RxSTATE <= RxType_idle;
				end
				else
					case (RxSTATE)
						RxType_idle :
							if (transmit == 1'b1)
							begin
								RxSTATE <= RxType_recieving;
								rx_shift_register <= 8'h00;
							end
							else if (SCLKSTATE == RxType_idle)
								done <= 1'b0;
						RxType_recieving :
							if (sck_previous == 1'b0 & sck_buffer == 1'b1)
							begin
								if (rx_count == 4'b1111)
								begin
									RxSTATE <= RxType_idle;
									rx_count <= 4'd0;
									rx_shift_register <= {rx_shift_register[6:0], sdi};
									done <= 1'b1;
								end
								else
								begin
									rx_count <= rx_count + 4'd1;
									rx_shift_register <= {rx_shift_register[6:0], sdi};
								end
							end
					endcase
			end
		end
		
		always @(posedge clk)
		begin: SCLKgen
			begin
				if (rst == 1'b1)
				begin
					clk_count <= 8'h00;
					SCLKSTATE <= SCLKType_idle;
					sck_previous <= 1'b1;
					sck_buffer <= 1'b1;
				end
				else
					case (SCLKSTATE)
						SCLKType_idle :
							begin
								sck_previous <= 1'b1;
								sck_buffer <= 1'b1;
								clk_count <= 8'h00;
								clk_edge_buffer <= 1'b0;
								
								if (transmit == 1'b1)
								begin
									SCLKSTATE <= SCLKType_running;
								end
							end
						SCLKType_running :
							if (done == 1'b1) begin
								SCLKSTATE <= SCLKType_idle;
							end
							else if (clk_count == CLKDIVIDER) begin
								if (clk_edge_buffer == 1'b0) begin
									sck_buffer <= 1'b1;
									clk_edge_buffer <= 1'b1;
								end
								else begin
									sck_buffer <= (~sck_buffer);
									clk_count <= 8'h00;
								end
							end
							else begin
								sck_previous <= sck_buffer;
								clk_count <= clk_count + 1'b1;
							end
					endcase
			end
		end
		
		assign rxbuffer = rx_shift_register;
		assign sclk = sck_buffer;
		assign done_out = done;
   
endmodule


