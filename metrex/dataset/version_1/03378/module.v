

`define FPGA_ADDR_MIN 'h0000
`define FPGA_ADDR_MAX 'h0400


module rx_engine  #(
  parameter C_DATA_WIDTH = 64                                    ) (
  input                         clk_i,                           input                         rst_n,                           input  [C_DATA_WIDTH-1:0]     m_axis_rx_tdata,
  input                         m_axis_rx_tlast,
  input                         m_axis_rx_tvalid,
  output reg                    m_axis_rx_tready,
  input                         compl_done_i,                    output reg                    req_compl_wd_o,                  output reg [31:0]             tx_reg_data_o,                   output reg [2:0]              req_tc_o,                        output reg                    req_td_o,                        output reg                    req_ep_o,                        output reg [1:0]              req_attr_o,                      output reg [9:0]              req_len_o,                       output reg [15:0]             req_rid_o,                       output reg [7:0]              req_tag_o,                       output reg [6:0]              req_addr_o,                      output reg [31:0]             reg_data_o,                      output reg                    reg_data_valid_o,                output reg [9:0]              reg_addr_o,                      input                         fpga_reg_wr_ack_i,               output reg                    fpga_reg_rd_o,                   input      [31:0]             reg_data_i,                      input                         fpga_reg_rd_ack_i,               output reg [7:0]              cpld_tag_o,
  output reg [31:0]             user_data_o,                     output reg [19:0]             user_addr_o,                     output reg                    user_wr_req_o,                   input      [31:0]             user_data_i,                     input                         user_rd_ack_i,                   output reg                    user_rd_req_o,                   output reg [63:0]             rcvd_data_o,                     output reg                    rcvd_data_valid_o                );

    wire               sop;
    reg [2:0]          state;
	 reg                in_packet_q;
    reg [31:0]         rx_tdata_p;
    reg                rcv_data;
	 reg                lock_tag;
	 reg                user_wr_ack;
	 
    localparam  IDLE           = 'd0,
	            SEND_DATA      = 'd1,
               WAIT_FPGA_DATA = 'd2,
               WAIT_USR_DATA  = 'd3,
               WAIT_TX_ACK    = 'd4,
               WR_DATA        = 'd5,
               RX_DATA        = 'd6;
					
    localparam MEM_RD = 7'b0000000,
               MEM_WR = 7'b1000000,
               CPLD   = 7'b1001010;
					
    assign sop            = !in_packet_q && m_axis_rx_tvalid; always@(posedge clk_i)
    begin
      if(!rst_n)
        in_packet_q <= 1'b0;
      else if (m_axis_rx_tvalid && m_axis_rx_tready && m_axis_rx_tlast)
        in_packet_q <= 1'b0;
      else if (sop && m_axis_rx_tready)
        in_packet_q <= 1'b1;
    end

   					
    always @ ( posedge clk_i ) 
    begin
        if (!rst_n ) begin
            m_axis_rx_tready <=  1'b0;
            req_compl_wd_o   <=  1'b0;
            state            <=  IDLE;
            user_rd_req_o    <=  1'b0;
            user_wr_req_o    <=  1'b0;
            rcv_data         <=  1'b0;
            fpga_reg_rd_o    <=  1'b0;
            reg_data_valid_o <=  1'b0;
        end 
        else 
        begin
            case (state)
                IDLE : begin
                    m_axis_rx_tready <=  1'b1;                  reg_data_valid_o <=  1'b0;
						  user_wr_req_o    <=  1'b0;
						  req_len_o        <=  m_axis_rx_tdata[9:0];  req_attr_o       <=  m_axis_rx_tdata[13:12];
                    req_ep_o         <=  m_axis_rx_tdata[14];
                    req_td_o         <=  m_axis_rx_tdata[15];
                    req_tc_o         <=  m_axis_rx_tdata[22:20];
                    req_rid_o        <=  m_axis_rx_tdata[63:48];
                    req_tag_o        <=  m_axis_rx_tdata[47:40];
                    if (sop) 
                    begin                                       if(m_axis_rx_tdata[30:24] == MEM_RD)      state    <=  SEND_DATA;
						      else if(m_axis_rx_tdata[30:24] == MEM_WR) state    <=  WR_DATA; 
                        else if(m_axis_rx_tdata[30:24] == CPLD)   begin
                           state    <=  RX_DATA;
									lock_tag <=  1'b1;
								end	
                    end
                end
                SEND_DATA: begin
                    if (m_axis_rx_tvalid && m_axis_rx_tlast)
                    begin
                        req_addr_o         <=  m_axis_rx_tdata[6:0];
                        m_axis_rx_tready   <=  1'b0;              user_addr_o        <=  m_axis_rx_tdata[19:0];
                        reg_addr_o         <=  m_axis_rx_tdata[9:0];
                        if(m_axis_rx_tdata[21:0] < `FPGA_ADDR_MAX) begin
                            state         <=  WAIT_FPGA_DATA; 
                            fpga_reg_rd_o <=  1'b1;   
                        end
                        else
                        begin
                           state         <=  WAIT_USR_DATA;
                           user_rd_req_o <=  1'b1;
                        end
                    end
                end
                WAIT_FPGA_DATA:begin
					     fpga_reg_rd_o    <=  1'b0; 
                    if(fpga_reg_rd_ack_i)
                    begin 
                        req_compl_wd_o   <=  1'b1;        tx_reg_data_o    <=  reg_data_i;
                        state            <=  WAIT_TX_ACK; end
                end
                WAIT_USR_DATA:begin
                    if(user_rd_ack_i)
                    begin
                        user_rd_req_o  <=  1'b0;
                        req_compl_wd_o <=  1'b1;
                        tx_reg_data_o  <=  user_data_i;
                        state          <=  WAIT_TX_ACK;
                    end
                end
                WAIT_TX_ACK: begin
                    if(compl_done_i)
                    begin
                       state            <=  IDLE;
                       req_compl_wd_o   <=  1'b0;
							  m_axis_rx_tready <=  1'b1;
                    end
                end
				WR_DATA:begin
                    reg_data_valid_o <=   1'b0;
                    user_wr_req_o    <=   1'b0;
                    if (m_axis_rx_tvalid && m_axis_rx_tlast)
                    begin
						      m_axis_rx_tready <=  1'b0;
                        reg_data_o       <=   m_axis_rx_tdata[63:32];
                        reg_addr_o       <=   m_axis_rx_tdata[9:0];
                        user_data_o      <=   m_axis_rx_tdata[63:32];
                        user_addr_o      <=   m_axis_rx_tdata[19:0];
                        if(m_axis_rx_tdata[21:0] < `FPGA_ADDR_MAX)  begin  
                            reg_data_valid_o <=   1'b1;    
                        end
                        else
                        begin
                            user_wr_req_o    <=   1'b1;
                        end
                    end
                    if (fpga_reg_wr_ack_i | user_wr_ack)
                    begin
                        state            <=   IDLE;   
                        m_axis_rx_tready <=   1'b1;								
                    end
				end
            RX_DATA:begin
				    lock_tag <= 1'b0;
                if(m_axis_rx_tvalid && m_axis_rx_tlast)
                begin
                    rcv_data  <=  1'b0;
                    state     <=  IDLE;
					m_axis_rx_tready <=  1'b1;
                end
                else
                    rcv_data  <=  1'b1;
            end
            endcase
        end
    end

    always @(posedge clk_i)
    begin
        rx_tdata_p <= m_axis_rx_tdata[63:32];
		  user_wr_ack <= user_wr_req_o;
        if(rcv_data & m_axis_rx_tvalid)
        begin
            rcvd_data_valid_o <= 1'b1;   
            rcvd_data_o       <= {rx_tdata_p,m_axis_rx_tdata[31:0]};
        end
        else
            rcvd_data_valid_o <= 1'b0;
    end
	 
	 always @(posedge clk_i)
	 begin
	     if(lock_tag)
	       cpld_tag_o <= m_axis_rx_tdata[15:8];
	 end

endmodule 
