module sd_card (
	output [31:0] io_lba,
	output reg    io_rd,
	output reg    io_wr,
	input			  io_ack,
	output		  io_conf,
	output		  io_sdhc,
	
	input	[7:0]	  io_din,
	input 		  io_din_strobe,

	output [7:0]  io_dout,
	input 		  io_dout_strobe,

	input         allow_sdhc,
	
   input         sd_cs,
   input         sd_sck,
   input         sd_sdi,
   output reg    sd_sdo
); 

reg req_io_rd = 1'b0; always @(posedge req_io_rd or posedge io_ack) begin
	if(io_ack) io_rd <= 1'b0;
	else 		  io_rd <= 1'b1;
end

reg req_io_wr = 1'b0; always @(posedge req_io_wr or posedge io_ack) begin
	if(io_ack) io_wr <= 1'b0;
	else 		  io_wr <= 1'b1;
end

wire [31:0] OCR = { 1'b0, io_sdhc, 30'h0 };  wire [7:0] READ_DATA_TOKEN = 8'hfe;

localparam NCR=4;

localparam RD_STATE_IDLE       = 2'd0;
localparam RD_STATE_WAIT_IO    = 2'd1;
localparam RD_STATE_SEND_TOKEN = 2'd2;
localparam RD_STATE_SEND_DATA  = 2'd3;
reg [1:0] read_state = RD_STATE_IDLE;  

localparam WR_STATE_IDLE       = 3'd0;
localparam WR_STATE_EXP_DTOKEN = 3'd1;
localparam WR_STATE_RECV_DATA  = 3'd2;
localparam WR_STATE_RECV_CRC0  = 3'd3;
localparam WR_STATE_RECV_CRC1  = 3'd4;
localparam WR_STATE_SEND_DRESP = 3'd5;
localparam WR_STATE_BUSY       = 3'd6;
reg [2:0] write_state = WR_STATE_IDLE;  

reg card_is_reset = 1'b0;    reg [6:0] sbuf; 
reg cmd55;
reg new_cmd_rcvd;
reg [7:0] cmd = 8'h00;
reg [2:0] bit_cnt;           reg [3:0] byte_cnt= 4'd15;   reg [31:0] lba;
assign io_lba = io_sdhc?lba:{9'd0, lba[31:9]};

reg [7:0] reply;
reg [7:0] reply0, reply1, reply2, reply3;
reg [3:0] reply_len;

wire rd_wait_io = (read_state != RD_STATE_IDLE);
reg rd_io_ack_i = 1'b0;
always @(negedge io_ack or negedge rd_wait_io) begin
	if(!rd_wait_io) rd_io_ack_i <= 1'b0;
	else            rd_io_ack_i <= 1'b1;
end
 
wire wr_wait_io = (write_state == WR_STATE_BUSY);
reg wr_io_ack_i = 1'b0;
always @(negedge io_ack or negedge wr_wait_io) begin
	if(!wr_wait_io) wr_io_ack_i <= 1'b0;
	else            wr_io_ack_i <= 1'b1;
end

reg wr_io_ack;
reg rd_io_ack;
always @(posedge sd_sck) begin	
	rd_io_ack <= rd_io_ack_i;
	wr_io_ack <= wr_io_ack_i;
end

reg [7:0] buffer [511:0];

reg [8:0] buffer_rptr;
reg buffer_read_strobe;
wire buffer_dout_strobe = buffer_read_strobe || io_dout_strobe;
reg [7:0] buffer_dout;
assign io_dout = buffer_dout;

reg buffer_read_sector_done;
reg buffer_read_ciscid_done;

always @(posedge buffer_dout_strobe or posedge new_cmd_rcvd) begin
	if(new_cmd_rcvd == 1) begin
		buffer_rptr <= 9'd0;
		buffer_read_sector_done <= 1'b0;
		buffer_read_ciscid_done <= 1'b0;
	end else begin
		buffer_dout <= buffer[buffer_rptr];
		buffer_rptr <= buffer_rptr + 9'd1;
		if(buffer_rptr == 511) buffer_read_sector_done <= 1'b1;
		if(buffer_rptr == 15)  buffer_read_ciscid_done <= 1'b1;
	end
end

reg [8:0] buffer_wptr;
reg buffer_write_strobe;
wire buffer_din_strobe = io_din_strobe || buffer_write_strobe;
wire [7:0] buffer_din = (cmd == 8'h51)?io_din:{sbuf, sd_sdi};

always @(posedge buffer_din_strobe or posedge new_cmd_rcvd) begin
	if(new_cmd_rcvd == 1)
		buffer_wptr <= 9'd0;
	else begin
		buffer[buffer_wptr] <= buffer_din;	
		buffer_wptr <= buffer_wptr + 9'd1;
	end
end

wire [7:0] WRITE_DATA_RESPONSE = 8'h05;

assign io_conf = (csd_wptr == 0);  reg [7:0] cid [15:0];
reg [7:0] csd [15:0];
reg [7:0] conf;

reg [7:0] cid_byte;
reg [7:0] csd_byte;
reg [5:0] csd_wptr = 6'd0;

wire io_has_sdhc = conf[0];
assign io_sdhc = allow_sdhc && io_has_sdhc;

always @(posedge io_din_strobe) begin
	if(!io_ack && (csd_wptr <= 32)) begin
	
		if(csd_wptr < 16)                       cid[csd_wptr[3:0]] <= io_din;	
		if((csd_wptr >= 16) && (csd_wptr < 32)) csd[csd_wptr[3:0]] <= io_din;	
		if(csd_wptr == 32)                      conf <= io_din;	
			
		csd_wptr	<= csd_wptr + 6'd1;
	end
end
 
always @(posedge buffer_dout_strobe) begin
	cid_byte <= cid[buffer_rptr[3:0]];
	csd_byte <= csd[buffer_rptr[3:0]];
end
 	
always@(negedge sd_sck) begin
	if(sd_cs == 0) begin
		buffer_read_strobe <= 1'b0;
		sd_sdo <= 1'b1;				req_io_rd <= 1'b0;
		
		if(byte_cnt == 5+NCR) begin
			sd_sdo <= reply[~bit_cnt];

			if(bit_cnt == 7) begin
				if((cmd == 8'h49)||(cmd == 8'h4a))
					read_state <= RD_STATE_SEND_TOKEN;      if(cmd == 8'h51) begin
					read_state <= RD_STATE_WAIT_IO;         req_io_rd <= 1'b1;                      end
			end
		end
		else if((reply_len > 0) && (byte_cnt == 5+NCR+1))
			sd_sdo <= reply0[~bit_cnt];
		else if((reply_len > 1) && (byte_cnt == 5+NCR+2))
			sd_sdo <= reply1[~bit_cnt];
		else if((reply_len > 2) && (byte_cnt == 5+NCR+3))
			sd_sdo <= reply2[~bit_cnt];
		else if((reply_len > 3) && (byte_cnt == 5+NCR+4))
			sd_sdo <= reply3[~bit_cnt];
		else
			sd_sdo <= 1'b1;

		case(read_state)
			RD_STATE_IDLE: ;
				RD_STATE_WAIT_IO: begin
				if(rd_io_ack && (bit_cnt == 7)) 
					read_state <= RD_STATE_SEND_TOKEN;
			end

			RD_STATE_SEND_TOKEN: begin
				sd_sdo <= READ_DATA_TOKEN[~bit_cnt];
	
				if(bit_cnt == 7) begin
					read_state <= RD_STATE_SEND_DATA;   buffer_read_strobe <= 1'b1;         end
			end
					
			RD_STATE_SEND_DATA: begin
				if(cmd == 8'h51) 							sd_sdo <= buffer_dout[~bit_cnt];
				else if(cmd == 8'h49) 					sd_sdo <= csd_byte[~bit_cnt];
				else if(cmd == 8'h4a) 					sd_sdo <= cid_byte[~bit_cnt];
				else
					sd_sdo <= 1'b1;

				if(bit_cnt == 7) begin
					if((cmd == 8'h51) && buffer_read_sector_done) read_state <= RD_STATE_IDLE;   else if(((cmd == 8'h49)||(cmd == 8'h4a)) && buffer_read_ciscid_done) read_state <= RD_STATE_IDLE;   else
						buffer_read_strobe <= 1'b1;    end
			end
		endcase
					
		if(write_state == WR_STATE_SEND_DRESP) 
			sd_sdo <= WRITE_DATA_RESPONSE[~bit_cnt];
			
		if(write_state == WR_STATE_BUSY) 
			sd_sdo <= 1'b0;
   end
end

reg illegal_write_state ;

always @(posedge sd_sck or posedge sd_cs) begin
	if(sd_cs == 1) begin
		bit_cnt <= 3'd0;
	end else begin 
		illegal_write_state <= 1'b0;
		new_cmd_rcvd <= 1'b0;
		buffer_write_strobe <= 1'b0;
		req_io_wr <= 1'b0;
		bit_cnt <= bit_cnt + 3'd1;
		
		if(bit_cnt != 7)
			sbuf[6:0] <= { sbuf[5:0], sd_sdi };
		else begin
			if(byte_cnt != 15)
				byte_cnt <= byte_cnt + 4'd1;			

			if((byte_cnt > 5) && (write_state == WR_STATE_IDLE) && 
				(read_state == RD_STATE_IDLE)  && sbuf[6:5] == 2'b01) begin
				byte_cnt <= 4'd0;			
				cmd <= { sbuf, sd_sdi};
				new_cmd_rcvd <= 1'b1;

			   cmd55 <= (cmd == 8'h77);
			end

			if(byte_cnt == 0) lba[31:24] <= { sbuf, sd_sdi};
			if(byte_cnt == 1) lba[23:16] <= { sbuf, sd_sdi};
			if(byte_cnt == 2) lba[15:8]  <= { sbuf, sd_sdi};
			if(byte_cnt == 3) lba[7:0]   <= { sbuf, sd_sdi};			

			if(byte_cnt == 4) begin		
		
				reply <= 8'h04;     reply_len <= 4'd0;  if(cmd == 8'h40) begin
					card_is_reset <= 1'b1;
					reply <= 8'h01;    end

				else if(card_is_reset) begin
					if(cmd == 8'h41)
						reply <= 8'h00;    else if(cmd == 8'h48) begin
						reply <= 8'h01;    reply0 <= 8'h00;
						reply1 <= 8'h00;
						reply2 <= 8'h01;
						reply3 <= 8'hAA;
						reply_len <= 4'd4;
					end
				
					else if(cmd == 8'h49)
						reply <= 8'h00;    else if(cmd == 8'h4a)
						reply <= 8'h00;    else if(cmd == 8'h50) begin
						if(lba == 32'd512)
							reply <= 8'h00;    else
							reply <= 8'h40;    end

					else if(cmd == 8'h51)
						reply <= 8'h00;    else if(cmd == 8'h58) begin
						reply <= 8'h00;    write_state <= WR_STATE_EXP_DTOKEN;  end

					else if(cmd55 && (cmd == 8'h69))
						reply <= 8'h00;    else if(cmd == 8'h77)
						reply <= 8'h01;    else if(cmd == 8'h7a) begin
						reply <= 8'h00;    reply0 <= OCR[31:24];   reply1 <= OCR[23:16];
						reply2 <= OCR[15:8];
						reply3 <= OCR[7:0];
						reply_len <= 4'd4;
					end
				end
			end
			
			case(write_state) 
				WR_STATE_IDLE: ;
				
				WR_STATE_EXP_DTOKEN:
					if({ sbuf, sd_sdi} == 8'hfe )
						write_state <= WR_STATE_RECV_DATA;

				WR_STATE_RECV_DATA: begin
					buffer_write_strobe <= 1'b1;

					if(buffer_wptr == 511)
						write_state <= WR_STATE_RECV_CRC0;
				end
	
				WR_STATE_RECV_CRC0:
					write_state <= WR_STATE_RECV_CRC1;

				WR_STATE_RECV_CRC1:
					write_state <= WR_STATE_SEND_DRESP;
	
				WR_STATE_SEND_DRESP: begin
					write_state <= WR_STATE_BUSY;
					req_io_wr <= 1'b1;               end
				
				WR_STATE_BUSY:
					if(wr_io_ack)
						write_state <= WR_STATE_IDLE;
						
				default:
					illegal_write_state <= 1'b1;
			endcase
		end
	end
end

endmodule
