

module ddr_ctrl_wrapper #(
	parameter ADDR_WIDTH	= 25	)
(
	output			rdy_o,
	output			idle_o,
	input  [31:0]		adr_i,
	output [31:0]		adr_o,
	input  [31:0]		dat_i,
	output [31:0]		dat_o,
	input  [3:0]		sel_i,
	input			acc_i,
	output			ack_o,
	input			we_i,
	input  [3:0]		buf_width_i,

	output [ADDR_WIDTH-3:0]	local_address_o,
	output			local_write_req_o,
	output			local_read_req_o,
	output			local_burstbegin_o,
	output [31:0]		local_wdata_o,
	output [3:0]		local_be_o,
	output [6:0]		local_size_o,
	input  [31:0]		local_rdata_i,
	input			local_rdata_valid_i,
	input			local_reset_n_i,
	input			local_clk_i,
	input			local_ready_i
);

	localparam LOCAL_ADR_WIDTH = ADDR_WIDTH-2;

	function [31:0] get_mask;
	input [3:0] width;
		begin
			get_mask = ((1 << (width)) - 1);
		end
	endfunction

	assign local_be_o	= sel_i;
	assign dat_o		= local_rdata_i;
	assign local_address_o	= we_i ? adr_i[LOCAL_ADR_WIDTH+1:2] : adr_i[LOCAL_ADR_WIDTH+1:2] & ~get_mask(buf_width_i);
	assign local_wdata_o	= dat_i;

	reg [22:0]	local_address;
	reg		local_write_req;
	reg		local_read_req;
	reg		local_burstbegin;
	reg [31:0]	local_wdata;
	reg [6:0]	local_size;

	assign local_write_req_o	= local_write_req;
	assign local_read_req_o		= local_read_req;
	assign local_burstbegin_o	= local_burstbegin;
	assign local_size_o		= local_size;

	reg [3:0]	state;
	reg [31:0]	count;
	reg		ack_w;
	reg [31:0]	adr;

	localparam [3:0]
		WAIT_READY    = 4'h0,
		IDLE          = 4'h1,
		WRITE         = 4'h2,
		READ          = 4'h3;

	assign rdy_o = local_ready_i;
	assign idle_o = (state == IDLE);
	assign adr_o = adr;

	assign ack_o = acc_i ? (we_i ? ack_w : local_rdata_valid_i) : 1'b0;

	always @(posedge local_clk_i) begin
		if (local_reset_n_i == 1'b0) begin
			local_write_req		<= 1'b0;
			local_read_req		<= 1'b0;
			local_burstbegin	<= 1'b0;
			local_size		<= 6'b1;
			count			<= 0;
			adr			<= 32'b0;
			state			<= WAIT_READY;
		end else begin

			ack_w			<= 1'b0;
			local_burstbegin	<= 1'b0;
			local_write_req		<= 1'b0;
			local_burstbegin	<= 1'b0;
			local_read_req		<= 1'b0;

			case (state)

			WAIT_READY: begin
				if (local_ready_i)
					state <= IDLE;
			end

			IDLE: begin
				if (acc_i) begin
					if (we_i & local_ready_i) begin
						ack_w			<= 1'b1;
						local_burstbegin	<= 1'b1;
						local_write_req		<= 1'b1;
						local_size		<= 1;
						state			<= WRITE;
					end
					if (!we_i & local_ready_i) begin
						local_burstbegin	<= 1'b1;
						local_read_req		<= 1'b1;
						state			<= READ;
						local_size		<= (1<<buf_width_i);
						adr			<= adr_i & ~get_mask(buf_width_i+2);
						count			<= 0;
					end
				end
			end

			WRITE : begin
				state <= IDLE;
			end

			READ : begin
				if (local_rdata_valid_i) begin
					count <= count + 1'b1;
					adr <= (adr & ~get_mask(buf_width_i+2)) | ((((adr >> 2) + 1) & get_mask(buf_width_i)) << 2);
				end

				if (count == (1<<buf_width_i)) begin
					count <= 0;
					state <= IDLE;
				end
			end


			endcase
		end
	end

endmodule
