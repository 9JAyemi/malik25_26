module SDCard(
input		wire			clk_i,			input		wire			cpuclk_n_i,		input		wire			reset_n_i,		input		wire			cs_i,				input		wire			adr_i,         input		wire			rw_n_i,			output	reg			halt_o,				input		wire	[7:0]	dat_i,			output	wire	[7:0]	dat_o,
	output	wire			irq_n_o,			output	wire			act_led_n_o,
	input		wire			card_detect_n_i,	input		wire			wp_locked_i,		output	reg			spi_ss_n_o,		output	reg			sclk_o,			output	reg			mosi_o,			input		wire			miso_i			);

reg							en_spi;
reg					[2:0]	state;
reg					[3:0]	bcnt;
reg							wffull;
reg					[1:0]	wffull_buf;
reg					[7:0]	rreg1;
reg					[7:0]	buffer1;
reg							wffull_reset;
reg					[2:0]	cd_buff0;
reg							irq_n;
reg							en_irq;
wire							irq_reset_n;
reg							halt_buf0;
reg							halt_buf1;
reg					[1:0]	halt_state;

assign dat_o = (!adr_i)	?	{!irq_n, 5'b00000, wp_locked_i, !card_detect_n_i}:	rreg1;																assign irq_reset_n =	~reset_n_i							?	1'b0:							~en_spi								?	1'b0:							~en_irq								?	1'b0:
																		1'b1;

assign irq_n_o = 			irq_n;

assign act_led_n_o = state[0];

always @(negedge cpuclk_n_i or posedge wffull_reset)
begin
	if(wffull_reset)
		wffull <= 1'b0;
	else
		if({cs_i, adr_i} == 2'b11)										begin
			wffull <= 1'b1;
		end
end

always @(negedge cpuclk_n_i or negedge reset_n_i)
begin
	if(!reset_n_i)
	begin
		halt_buf0 <= 1'b0; 
		halt_buf1 <= 1'b0;
		halt_state <= 2'b00;
		halt_o <= 1'b0;
	end
	else
	begin
		halt_buf0 <= !state[0];			halt_buf1 <= halt_buf0;
		case(halt_state)
		2'b00:
		begin
			if({cs_i, adr_i, en_spi}== 3'b111)		begin
				halt_o <= 1'b1;				halt_state <= 2'b01;
			end
		end
		2'b01:
		begin
			if(halt_buf1)						halt_state <= 2'b10;
		end
		2'b10:
		begin
			if(!halt_buf1)						begin
				halt_state <= 2'b00;
				halt_o <= 1'b0;				end
		end
		2'b11:									begin
			halt_state <= 2'b00;
		end
		endcase
	end
end

always @(negedge cpuclk_n_i or negedge reset_n_i)
begin
	if(!reset_n_i)
	begin
		spi_ss_n_o <= 1'b1;
		en_irq <= 1'b0;
		en_spi <= 1'b0;
		buffer1 <= 8'hFF;
	end
	else
	begin
		case ({cs_i, rw_n_i, adr_i})
		3'b100:																		begin
			spi_ss_n_o <= !dat_i[0]|!dat_i[7];								en_irq <= dat_i[6];
			en_spi <= dat_i[7];
		end
		3'b101:																		begin
			buffer1 <= dat_i;
		end
		3'b111:																		begin																			buffer1 <= 8'hFF;
		end
		endcase
	end
end

always @(negedge cpuclk_n_i)
begin
	if(!irq_reset_n)																begin
		irq_n <= 1'b1;
		cd_buff0 <= 3'b000;
	end
	else
	begin
		cd_buff0 <= ({cd_buff0[1], cd_buff0[0], card_detect_n_i});			if(cd_buff0 == 3'b100)															irq_n <= 1'b0;
	end
end

always @(posedge clk_i)
begin
	if (~en_spi)
	begin
		state <= 3'b001; 				bcnt  <= 4'h0;
		sclk_o <= 1'b0;
		wffull_buf <= 2'b00;
		wffull_reset <= 1'b1;		rreg1 <= 8'h00;
	end
	else
	begin
		wffull_buf <= {wffull_buf[0], wffull};
		case (state)
		3'b001:								begin
			sclk_o <= 1'b0;				wffull_reset <= 1'b0;
			if (wffull_buf[1])
			begin
				bcnt  <= 4'h0;				rreg1 <= buffer1;
				state <= 3'b010;
			end
		end
		3'b010:								begin
			sclk_o   <= 1'b0;
			wffull_reset <= 1'b1;
			state   <= 3'b100;
			if (bcnt[3])
			begin
				state <= 3'b001;
				wffull_reset <= 1'b0;
				mosi_o <= 1'b1;
			end
			else
			begin
				state <= 3'b100;
				wffull_reset <= 1'b1;
				mosi_o <= rreg1[7];
			end
		end

		3'b100:								begin
			state <= 3'b010;
			sclk_o <= 1'b1;
			rreg1 <= {rreg1[6:0], miso_i};
			bcnt <= bcnt + 4'h1;
		end
		default:
		begin
			state <= 3'b001;
		end
		endcase
	end
end

endmodule
