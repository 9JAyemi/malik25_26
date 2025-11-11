

module lcd_ctrl #(
	parameter WB_CLOCK_FREQUENCY = 50_000_000
)
(
	input		wb_clk_i,
	input		wb_rst_i,

	output		hsync_n_o,
	output		vsync_n_o,
	output		blank_n_o,
	output	[7:0]	lcd_data_o,
	output		lcd_rst_n_o,

	output		lcd_scen_o,
	output		lcd_scl_o,
	output		lcd_sda_o,

	input		pixel_clk_i,
	input		pixel_rst_i,

	input		hsync_i,
	input		vsync_i,
	input		blank_i,
	input [7:0]	r_i,
	input [7:0]	g_i,
	input [7:0]	b_i
);

	localparam [3:0]
		LCD_RESET   = 4'h0,
		START_DELAY = 4'h1,
		IDLE        = 4'h2,
		DELAY_INIT  = 4'h3,
		START_XFER  = 4'h4,
		CLK_PULSE_0 = 4'h5,
		CLK_PULSE_1 = 4'h6,
		DONE        = 4'h7,
		WAIT        = 4'h8;

	localparam BIT_DELAY     = 100 * (WB_CLOCK_FREQUENCY / 1000000); localparam STARTUP_DELAY = 100 * (WB_CLOCK_FREQUENCY / 1000);    localparam RESET_DELAY   = 20  * (WB_CLOCK_FREQUENCY / 1000);    reg [4:0]	state;

	reg		lcd_scen;
	reg		lcd_scl;
	reg		lcd_sda;
	reg		lcd_req;

	reg [15:0]	lcd_serial_dat;
	reg [5:0]	lcd_serial_adr;
	reg [7:0]	lcd_serial_reg;

	assign		lcd_scen_o = lcd_scen;
	assign		lcd_scl_o = lcd_scl;
	assign		lcd_sda_o = lcd_sda;

	reg [7:0]	cur_reg;
	reg [4:0]	bit_idx;
	reg		lcd_rst_n;

	integer		delay;

	localparam NB_INIT_REGS  = 19;

	reg [15:0]	init_values [0:31];

	initial begin
		init_values[0] = {6'h11, 2'b00, 8'h05};
		init_values[1] = {6'h12, 2'b00, 8'h6A};
		init_values[2] = {6'h13, 2'b00, 8'hFF};
		init_values[3] = {6'h14, 2'b00, 8'h6A};
		init_values[4] = {6'h15, 2'b00, 8'hC8};
		init_values[5] = {6'h16, 2'b00, 8'h21};
		init_values[6] = {6'h17, 2'b00, 8'h77};
		init_values[7] = {6'h18, 2'b00, 8'hCC};
		init_values[8] = {6'h19, 2'b00, 8'h1F};
		init_values[9] = {6'h1A, 2'b00, 8'h71};
		init_values[10] = {6'h1B, 2'b00, 8'hC1};
		init_values[11] = {6'h1C, 2'b00, 8'h11};
		init_values[12] = {6'h1D, 2'b00, 8'h60};
		init_values[13] = {6'h1E, 2'b00, 8'hAE};
		init_values[14] = {6'h1F, 2'b00, 8'hFC};
		init_values[15] = {6'h20, 2'b00, 8'hF0};
		init_values[16] = {6'h21, 2'b00, 8'hF0};

		init_values[17] = {6'h03, 2'b00, 8'h5F};

		init_values[18] = {6'h02, 2'b00, 8'h07};
	end

	assign	lcd_rst_n_o = lcd_rst_n;

	always @(posedge wb_clk_i or posedge wb_rst_i)
		if (wb_rst_i) begin
			state		<= LCD_RESET;
			lcd_scen	<= 1'b1;
			lcd_scl		<= 1'b0;
			lcd_sda		<= 1'b1;
			cur_reg		<= 0;
			bit_idx		<= 0;
			lcd_req		<= 1'b1;
			lcd_rst_n	<= 1'b0;
		end else begin
			case (state)

			LCD_RESET: begin
				if (delay < RESET_DELAY)
					delay <= delay + 1;
				else begin
					delay <= 0;
					lcd_rst_n <= 1'b1;
					state <= START_DELAY;
				end
			end

			START_DELAY: begin
				if (delay < STARTUP_DELAY)
					delay <= delay + 1;
				else begin
					delay <= 0;
					state <= IDLE;
				end
			end

			IDLE: begin
				if (cur_reg < (NB_INIT_REGS - 1))
					cur_reg <= cur_reg + 1;
				else
					lcd_req <= 1'b0;

				lcd_serial_dat <= init_values[cur_reg];
				if (lcd_req) begin
					lcd_scen	<= 1'b0;
					bit_idx		<= 0;
					delay		<= 0;
					state		<= DELAY_INIT;
				end
			end

			DELAY_INIT: begin
				if (delay < BIT_DELAY)
					delay	<= delay + 1;
				else begin
					delay	<= 0;
					state	<= START_XFER;
				end
			end

			START_XFER: begin
				lcd_sda <= lcd_serial_dat[15-bit_idx];
				if (bit_idx < 16) begin
					state	<= CLK_PULSE_0;
				end else begin
					lcd_sda	<= 1'b0;
					delay	<= 0;
					state	<= DONE;
				end
			end

			CLK_PULSE_0: begin
				if (delay < BIT_DELAY)
					delay	<= delay + 1;
				else begin
					delay	<= 0;
					state	<= CLK_PULSE_1;
					lcd_scl	<= 1'b1;
				end
			end

			CLK_PULSE_1: begin
				if (delay < BIT_DELAY)
					delay	<= delay + 1;
				else begin
					delay	<= 0;
					lcd_scl	<= 1'b0;
					state	<= START_XFER;
					bit_idx	<= bit_idx + 1;
				end
			end

			DONE: begin
				if (delay < BIT_DELAY)
					delay	<= delay + 1;
				else begin
					lcd_scen<= 1'b1;
					delay	<= 0;
					if (lcd_req)
						state <= WAIT;
				end
			end

			WAIT: begin
				if (delay < BIT_DELAY)
					delay	<= delay + 1;
				else
					state	<= IDLE;
			end

			endcase
		end

	reg [1:0]	pix_count;

	reg		hsync_r, hsync_r2;
	reg		vsync_r, vsync_r2;
	reg		blank_r, blank_r2;
	reg [7:0]	r_r, r_r2;
	reg [7:0]	g_r, g_r2;
	reg [7:0]	b_r, b_r2;

	assign hsync_n_o = hsync_r2;
	assign vsync_n_o = vsync_r2;
	assign blank_n_o = blank_r2;

	assign lcd_data_o = (pix_count == 0) ? b_r2 : (pix_count == 1) ? r_r2 : g_r2;

	always @(posedge pixel_clk_i or posedge pixel_rst_i)
	begin
		if (pixel_rst_i == 1) begin
			pix_count	<= 2'b0;
		end else begin

			hsync_r2 <= hsync_r; hsync_r <= ~hsync_i;
			vsync_r2 <= vsync_r; vsync_r <= ~vsync_i;
			blank_r2 <= blank_r; blank_r <= ~blank_i;

			r_r2 <= r_r; r_r <= r_i;
			g_r2 <= g_r; g_r <= g_i;
			b_r2 <= b_r; b_r <= b_i;

			if (pix_count < 2)
				pix_count <= pix_count + 1;
			else
				pix_count <= 0;

			if (hsync_r2 && !hsync_r)
				pix_count <= 0;

			end
	end

endmodule


