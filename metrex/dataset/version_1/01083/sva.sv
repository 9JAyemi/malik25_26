// SVA for pcieCore_axi_basic_rx_null_gen
// Bind this file to the DUT. Focused, parameter-aware, checks key FSM/counter/outputs and covers key scenarios.

module pcieCore_axi_basic_rx_null_gen_sva #(
  parameter int C_DATA_WIDTH = 128,
  parameter int KEEP_WIDTH   = C_DATA_WIDTH/8
)(
  input  logic                       user_clk,
  input  logic                       user_rst,

  // AXIS RX
  input  logic [C_DATA_WIDTH-1:0]    m_axis_rx_tdata,
  input  logic                       m_axis_rx_tvalid,
  input  logic                       m_axis_rx_tready,
  input  logic                       m_axis_rx_tlast,
  input  logic [21:0]                m_axis_rx_tuser,

  // DUT outputs
  input  logic                       null_rx_tvalid,
  input  logic                       null_rx_tlast,
  input  logic [KEEP_WIDTH-1:0]      null_rx_tkeep,
  input  logic                       null_rdst_rdy,
  input  logic [4:0]                 null_is_eof,

  // DUT internals (bound hierarchically)
  input  logic                       cur_state,
  input  logic                       next_state,
  input  logic [11:0]                reg_pkt_len_counter,
  input  logic [11:0]                pkt_len_counter,
  input  logic [11:0]                new_pkt_len,
  input  logic                       pkt_done,
  input  logic                       straddle_sof,
  input  logic [KEEP_WIDTH-1:0]      eof_tkeep,
  input  logic                       eof
);

  // Derived constants
  localparam int unsigned IFW = (C_DATA_WIDTH==128) ? 4 :
                                (C_DATA_WIDTH==64)  ? 2 : 1;

  // Basic sanity
  // Reset behavior
  assert property (@(posedge user_clk) user_rst |-> (cur_state==1'b0 && reg_pkt_len_counter==12'h0));

  // Legal states
  assert property (@(posedge user_clk) disable iff(user_rst) (cur_state inside {1'b0,1'b1}) && (next_state inside {1'b0,1'b1}));

  // Registered next-state/next-counter
  assert property (@(posedge user_clk) disable iff(user_rst) (cur_state==$past(next_state) && reg_pkt_len_counter==$past(pkt_len_counter)));

  // IDLE counter update
  assert property (@(posedge user_clk) disable iff(user_rst) (cur_state==1'b0) |=> (reg_pkt_len_counter==$past(new_pkt_len)));

  // IDLE->IN_PACKET on handshake and not eof
  assert property (@(posedge user_clk) disable iff(user_rst)
                   (cur_state==1'b0 && m_axis_rx_tvalid && m_axis_rx_tready && !eof) |=> (cur_state==1'b1));

  // IDLE hold when not starting a packet
  assert property (@(posedge user_clk) disable iff(user_rst)
                   (cur_state==1'b0 && !(m_axis_rx_tvalid && m_axis_rx_tready && !eof)) |=> (cur_state==1'b0));

  // IN_PACKET straddle (128b only): reload length and stay in packet
  generate if (C_DATA_WIDTH==128) begin
    assert property (@(posedge user_clk) disable iff(user_rst)
                     (cur_state==1'b1 && straddle_sof && m_axis_rx_tvalid) |=> (cur_state==1'b1 && reg_pkt_len_counter==$past(new_pkt_len)));
  end endgenerate

  // IN_PACKET: done on ready => go IDLE and reload
  assert property (@(posedge user_clk) disable iff(user_rst)
                   (cur_state==1'b1 && m_axis_rx_tready && pkt_done
                    && (!(C_DATA_WIDTH==128) || !straddle_sof)) |=> (cur_state==1'b0 && reg_pkt_len_counter==$past(new_pkt_len)));

  // IN_PACKET: decrement on ready when not done and not straddle reload
  assert property (@(posedge user_clk) disable iff(user_rst)
                   (cur_state==1'b1 && m_axis_rx_tready && !pkt_done
                    && (!(C_DATA_WIDTH==128) || !straddle_sof)) |=> (cur_state==1'b1 && reg_pkt_len_counter==$past(reg_pkt_len_counter)-IFW));

  // IN_PACKET: hold counter when not ready and not straddle reload
  assert property (@(posedge user_clk) disable iff(user_rst)
                   (cur_state==1'b1 && !m_axis_rx_tready
                    && (!(C_DATA_WIDTH==128) || !straddle_sof)) |=> (cur_state==1'b1 && reg_pkt_len_counter==$past(reg_pkt_len_counter)));

  // No underflow on decrement path
  assert property (@(posedge user_clk) disable iff(user_rst)
                   (cur_state==1'b1 && m_axis_rx_tready && !pkt_done
                    && (!(C_DATA_WIDTH==128) || !straddle_sof)) |-> ($past(reg_pkt_len_counter) > IFW[11:0]));

  // Straddle must be 0 for widths !=128
  generate if (C_DATA_WIDTH!=128) begin
    assert property (@(posedge user_clk) disable iff(user_rst) (straddle_sof==1'b0));
  end endgenerate

  // Output invariants
  assert property (@(posedge user_clk) disable iff(user_rst) null_rx_tvalid); // always high
  assert property (@(posedge user_clk) disable iff(user_rst) (null_rdst_rdy == null_rx_tlast));
  assert property (@(posedge user_clk) disable iff(user_rst) (null_rx_tlast == (pkt_len_counter <= IFW[11:0])));
  assert property (@(posedge user_clk) disable iff(user_rst) (null_rx_tlast |-> (null_rx_tkeep==eof_tkeep)));
  assert property (@(posedge user_clk) disable iff(user_rst) (!null_rx_tlast |-> (null_rx_tkeep=={KEEP_WIDTH{1'b1}})));

  // eof_tkeep mapping by width
  generate
    if (C_DATA_WIDTH==128) begin
      assert property (@(posedge user_clk) disable iff(user_rst) (eof_tkeep=={KEEP_WIDTH{1'b0}}));
    end else if (C_DATA_WIDTH==64) begin
      assert property (@(posedge user_clk) disable iff(user_rst)
                       (eof_tkeep == { ((pkt_len_counter==12'd2)? 4'hF:4'h0), 4'hF }));
    end else begin
      assert property (@(posedge user_clk) disable iff(user_rst) (eof_tkeep==4'hF));
    end
  endgenerate

  // null_is_eof mapping
  generate
    if (C_DATA_WIDTH==128) begin
      assert property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd1) |-> (null_is_eof==5'b10011));
      assert property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd2) |-> (null_is_eof==5'b10111));
      assert property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd3) |-> (null_is_eof==5'b11011));
      assert property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd4) |-> (null_is_eof==5'b11111));
      assert property (@(posedge user_clk) disable iff(user_rst)
                       (!(pkt_len_counter inside {12'd1,12'd2,12'd3,12'd4})) |-> (null_is_eof==5'b00011));
    end else if (C_DATA_WIDTH==64) begin
      assert property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd1) |-> (null_is_eof==5'b10011));
      assert property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd2) |-> (null_is_eof==5'b10111));
      assert property (@(posedge user_clk) disable iff(user_rst)
                       (!(pkt_len_counter inside {12'd1,12'd2})) |-> (null_is_eof==5'b00011));
    end else begin
      assert property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd1) |-> (null_is_eof==5'b10011));
      assert property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter!=12'd1) |-> (null_is_eof==5'b00011));
    end
  endgenerate

  // Coverage
  // Basic packet start/finish
  cover property (@(posedge user_clk) disable iff(user_rst)
                  cur_state==1'b0 ##1 (m_axis_rx_tvalid && m_axis_rx_tready && !eof) ##1 cur_state==1'b1);

  cover property (@(posedge user_clk) disable iff(user_rst)
                  cur_state==1'b1 ##[1:$] (m_axis_rx_tready && pkt_done && (!(C_DATA_WIDTH==128) || !straddle_sof)) ##1 cur_state==1'b0);

  // Decrement path with a stall
  cover property (@(posedge user_clk) disable iff(user_rst)
                  cur_state==1'b1 && !pkt_done && m_axis_rx_tready
                  ##1 cur_state==1'b1 && !m_axis_rx_tready
                  ##1 cur_state==1'b1 && m_axis_rx_tready && !pkt_done);

  // Straddle coverage (128b)
  generate if (C_DATA_WIDTH==128) begin
    cover property (@(posedge user_clk) disable iff(user_rst) (cur_state==1'b1 && straddle_sof && m_axis_rx_tvalid));
    cover property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd1));
    cover property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd2));
    cover property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd3));
    cover property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd4));
  end else if (C_DATA_WIDTH==64) begin
    cover property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd1));
    cover property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd2));
  end else begin
    cover property (@(posedge user_clk) disable iff(user_rst) (pkt_len_counter==12'd1));
  end endgenerate

endmodule

// Bind into DUT
bind pcieCore_axi_basic_rx_null_gen
  pcieCore_axi_basic_rx_null_gen_sva #(.C_DATA_WIDTH(C_DATA_WIDTH), .KEEP_WIDTH(KEEP_WIDTH)) pcieCore_axi_basic_rx_null_gen_sva_i (
    .user_clk(user_clk),
    .user_rst(user_rst),

    .m_axis_rx_tdata(m_axis_rx_tdata),
    .m_axis_rx_tvalid(m_axis_rx_tvalid),
    .m_axis_rx_tready(m_axis_rx_tready),
    .m_axis_rx_tlast(m_axis_rx_tlast),
    .m_axis_rx_tuser(m_axis_rx_tuser),

    .null_rx_tvalid(null_rx_tvalid),
    .null_rx_tlast(null_rx_tlast),
    .null_rx_tkeep(null_rx_tkeep),
    .null_rdst_rdy(null_rdst_rdy),
    .null_is_eof(null_is_eof),

    .cur_state(cur_state),
    .next_state(next_state),
    .reg_pkt_len_counter(reg_pkt_len_counter),
    .pkt_len_counter(pkt_len_counter),
    .new_pkt_len(new_pkt_len),
    .pkt_done(pkt_done),
    .straddle_sof(straddle_sof),
    .eof_tkeep(eof_tkeep),
    .eof(eof)
  );