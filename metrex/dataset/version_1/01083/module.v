

module pcieCore_axi_basic_rx_null_gen # (
  parameter C_DATA_WIDTH = 128,           parameter TCQ = 1,                      parameter KEEP_WIDTH = C_DATA_WIDTH / 8            ) (

  input      [C_DATA_WIDTH-1:0] m_axis_rx_tdata,     input                         m_axis_rx_tvalid,    input                         m_axis_rx_tready,    input                         m_axis_rx_tlast,     input                  [21:0] m_axis_rx_tuser,     output                        null_rx_tvalid,      output                        null_rx_tlast,       output       [KEEP_WIDTH-1:0] null_rx_tkeep,       output                        null_rdst_rdy,       output reg              [4:0] null_is_eof,         input                         user_clk,            input                         user_rst             );


localparam INTERFACE_WIDTH_DWORDS = (C_DATA_WIDTH == 128) ? 11'd4 :
                                           (C_DATA_WIDTH == 64) ? 11'd2 : 11'd1;

localparam            IDLE      = 0;
localparam            IN_PACKET = 1;
reg                   cur_state;
reg                   next_state;

reg            [11:0] reg_pkt_len_counter;
reg            [11:0] pkt_len_counter;
wire           [11:0] pkt_len_counter_dec;
wire                  pkt_done;

wire           [11:0] new_pkt_len;
wire            [9:0] payload_len;
wire            [1:0] packet_fmt;
wire                  packet_td;
reg             [3:0] packet_overhead;

wire [KEEP_WIDTH-1:0] eof_tkeep;
wire                  straddle_sof;
wire                  eof;


assign eof = m_axis_rx_tuser[21];
generate
  if(C_DATA_WIDTH == 128) begin : sof_eof_128
    assign straddle_sof = (m_axis_rx_tuser[14:13] == 2'b11);
  end
  else begin : sof_eof_64_32
    assign straddle_sof = 1'b0;
  end
endgenerate


generate
  if(C_DATA_WIDTH == 128) begin : len_calc_128
    assign packet_fmt  = straddle_sof ?
                                m_axis_rx_tdata[94:93] : m_axis_rx_tdata[30:29];
    assign packet_td   = straddle_sof ?
                                      m_axis_rx_tdata[79] : m_axis_rx_tdata[15];
    assign payload_len = packet_fmt[1] ?
         (straddle_sof ? m_axis_rx_tdata[73:64] : m_axis_rx_tdata[9:0]) : 10'h0;

    always @(*) begin
      case({packet_fmt[0], packet_td, straddle_sof})
        3'b0_0_0: packet_overhead = 4'd3 + 4'd0 - 4'd4;
        3'b0_0_1: packet_overhead = 4'd3 + 4'd0 - 4'd2;
        3'b0_1_0: packet_overhead = 4'd3 + 4'd1 - 4'd4;
        3'b0_1_1: packet_overhead = 4'd3 + 4'd1 - 4'd2;
        3'b1_0_0: packet_overhead = 4'd4 + 4'd0 - 4'd4;
        3'b1_0_1: packet_overhead = 4'd4 + 4'd0 - 4'd2;
        3'b1_1_0: packet_overhead = 4'd4 + 4'd1 - 4'd4;
        3'b1_1_1: packet_overhead = 4'd4 + 4'd1 - 4'd2;
      endcase
    end
  end
  else if(C_DATA_WIDTH == 64) begin : len_calc_64
    assign packet_fmt  = m_axis_rx_tdata[30:29];
    assign packet_td   = m_axis_rx_tdata[15];
    assign payload_len = packet_fmt[1] ? m_axis_rx_tdata[9:0] : 10'h0;

    always @(*) begin
      case({packet_fmt[0], packet_td})
        2'b0_0: packet_overhead = 4'd3 + 4'd0 - 4'd2;
        2'b0_1: packet_overhead = 4'd3 + 4'd1 - 4'd2;
        2'b1_0: packet_overhead = 4'd4 + 4'd0 - 4'd2;
        2'b1_1: packet_overhead = 4'd4 + 4'd1 - 4'd2;
      endcase
    end
  end
  else begin : len_calc_32
    assign packet_fmt  = m_axis_rx_tdata[30:29];
    assign packet_td   = m_axis_rx_tdata[15];
    assign payload_len = packet_fmt[1] ? m_axis_rx_tdata[9:0] : 10'h0;

    always @(*) begin
      case({packet_fmt[0], packet_td})
        2'b0_0: packet_overhead = 4'd3 + 4'd0 - 4'd1;
        2'b0_1: packet_overhead = 4'd3 + 4'd1 - 4'd1;
        2'b1_0: packet_overhead = 4'd4 + 4'd0 - 4'd1;
        2'b1_1: packet_overhead = 4'd4 + 4'd1 - 4'd1;
      endcase
    end
  end
endgenerate

assign new_pkt_len =
         {{9{packet_overhead[3]}}, packet_overhead[2:0]} + {2'b0, payload_len};


assign pkt_len_counter_dec = reg_pkt_len_counter - INTERFACE_WIDTH_DWORDS;
assign pkt_done = (reg_pkt_len_counter <= INTERFACE_WIDTH_DWORDS);

always @(*) begin
  case (cur_state)

    IDLE: begin
      if(m_axis_rx_tvalid && m_axis_rx_tready && !eof) begin
        next_state = IN_PACKET;
      end
      else begin
        next_state = IDLE;
      end

      pkt_len_counter = new_pkt_len;
    end

    IN_PACKET: begin
      if((C_DATA_WIDTH == 128) && straddle_sof && m_axis_rx_tvalid) begin
        pkt_len_counter = new_pkt_len;
        next_state = IN_PACKET;
      end

      else if(m_axis_rx_tready && pkt_done)
      begin
        pkt_len_counter = new_pkt_len;
        next_state      = IDLE;
      end

      else begin
        if(m_axis_rx_tready) begin
          pkt_len_counter = pkt_len_counter_dec;
        end
        else begin
          pkt_len_counter = reg_pkt_len_counter;
        end

        next_state = IN_PACKET;
      end
    end

    default: begin
      pkt_len_counter = reg_pkt_len_counter;
      next_state      = IDLE;
    end
  endcase
end


always @(posedge user_clk) begin
  if(user_rst) begin
    cur_state           <= #TCQ IDLE;
    reg_pkt_len_counter <= #TCQ 12'h0;
  end
  else begin
    cur_state           <= #TCQ next_state;
    reg_pkt_len_counter <= #TCQ pkt_len_counter;
  end
end


generate
  if(C_DATA_WIDTH == 128) begin : strb_calc_128
    always @(*) begin
      case(pkt_len_counter)
        10'd1:   null_is_eof = 5'b10011;
        10'd2:   null_is_eof = 5'b10111;
        10'd3:   null_is_eof = 5'b11011;
        10'd4:   null_is_eof = 5'b11111;
        default: null_is_eof = 5'b00011;
      endcase
    end

    assign eof_tkeep = {KEEP_WIDTH{1'b0}};
  end
  else if(C_DATA_WIDTH == 64) begin : strb_calc_64
    always @(*) begin
      case(pkt_len_counter)
        10'd1:   null_is_eof = 5'b10011;
        10'd2:   null_is_eof = 5'b10111;
        default: null_is_eof = 5'b00011;
      endcase
    end

    assign eof_tkeep = { ((pkt_len_counter == 12'd2) ? 4'hF:4'h0), 4'hF };
  end
  else begin : strb_calc_32
    always @(*) begin
      if(pkt_len_counter == 12'd1) begin
        null_is_eof = 5'b10011;
      end
      else begin
        null_is_eof = 5'b00011;
      end
    end

    assign eof_tkeep = 4'hF;
  end
endgenerate


assign null_rx_tvalid = 1'b1;
assign null_rx_tlast  = (pkt_len_counter <= INTERFACE_WIDTH_DWORDS);
assign null_rx_tkeep  = null_rx_tlast ? eof_tkeep : {KEEP_WIDTH{1'b1}};
assign null_rdst_rdy  = null_rx_tlast;

endmodule
