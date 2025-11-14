// SVA for uart_tx
// Bind-in checker that leverages internal design state to verify protocol and datapath

module uart_tx_sva #(
  parameter DATA_WIDTH = 8
)(
  input  logic                   clk,
  input  logic                   rst,
  // DUT ports
  input  logic [DATA_WIDTH-1:0]  s_axis_tdata,
  input  logic                   s_axis_tvalid,
  input  logic                   s_axis_tready,
  input  logic                   txd,
  input  logic                   busy,
  input  logic [15:0]            prescale,
  // DUT internals
  input  logic                   s_axis_tready_reg,
  input  logic                   txd_reg,
  input  logic                   busy_reg,
  input  logic [DATA_WIDTH:0]    data_reg,
  input  logic [18:0]            prescale_reg,
  input  logic [3:0]             bit_cnt
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst)

  // Basic param/port sanity
  initial assert (DATA_WIDTH <= 14) else $error("DATA_WIDTH too large for 4-bit bit_cnt");

  // Outputs match regs
  assert property (s_axis_tready == s_axis_tready_reg);
  assert property (txd == txd_reg);
  assert property (busy == busy_reg);

  // Reset state
  assert property (rst |=> (s_axis_tready_reg==0 && txd_reg==1 && prescale_reg==0 && bit_cnt==0 && busy_reg==0));

  // Handshake only when idle
  assert property ((s_axis_tvalid && s_axis_tready) |-> (prescale_reg==0 && bit_cnt==0));

  // Accept: load shifter/start bit/busy, toggle ready as coded
  assert property (
    (s_axis_tvalid && s_axis_tready)
    |=> (prescale_reg == (prescale<<3)-1
      && bit_cnt == DATA_WIDTH+1
      && data_reg == {1'b1, $past(s_axis_tdata)}
      && txd_reg == 0
      && busy_reg == 1
      && s_axis_tready_reg == ~$past(s_axis_tready_reg))
  );

  // While ticking prescale, it strictly decrements and ready stays low
  assert property ((prescale_reg>0) |=> (prescale_reg == $past(prescale_reg)-1 && s_axis_tready_reg==0));

  // Shift behavior on data bits (prescale boundary, not last data/stop)
  assert property (
    (prescale_reg==0 && bit_cnt>1)
    |=> (bit_cnt == $past(bit_cnt)-1
      && prescale_reg == (prescale<<3)-1
      && txd_reg == $past(data_reg[0])
      && data_reg == {1'b0, $past(data_reg[DATA_WIDTH:1])})
  );

  // Stop bit load on last data-to-stop transition
  assert property (
    (prescale_reg==0 && bit_cnt==1)
    |=> (bit_cnt == 0 && prescale_reg == (prescale<<3) && txd_reg == 1)
  );

  // End-of-frame: last prescale tick to idle (ready high, busy low, txd idle high)
  assert property (
    ($past(prescale_reg==1) && $past(bit_cnt==0))
    |=> (prescale_reg==0 && bit_cnt==0 && s_axis_tready_reg==1 && busy_reg==0 && txd_reg==1)
  );

  // Busy must indicate in-frame (either bits remaining or stop-bit timing active)
  assert property (((prescale_reg>0) || (bit_cnt>0)) |-> busy_reg==1);

  // Idle implies txd high
  assert property (((prescale_reg==0) && (bit_cnt==0)) |-> txd_reg==1);

  // Optional environment assumption: prescale nonzero when accepting a frame
  assume property ((s_axis_tvalid && s_axis_tready) |-> (prescale != 16'd0));

  // Lightweight scoreboard for LSB-first data verification at each shift
  logic [DATA_WIDTH-1:0] hdata;
  logic [4:0]            bit_idx;
  always_ff @(posedge clk) begin
    if (rst) begin
      hdata  <= '0;
      bit_idx<= '0;
    end else begin
      if (s_axis_tvalid && s_axis_tready) begin
        hdata   <= s_axis_tdata;
        bit_idx <= '0;
      end else if (prescale_reg==0 && bit_cnt>1) begin
        bit_idx <= bit_idx + 1'b1;
      end
    end
  end
  assert property ((prescale_reg==0 && bit_cnt>1) |-> (txd_reg == hdata[bit_idx]));

  // Functional coverage
  cover property (s_axis_tvalid && s_axis_tready); // any accept
  cover property ((s_axis_tvalid && s_axis_tready && s_axis_tdata=='0)
                  ##[1:$] (prescale_reg==0 && bit_cnt==0 && busy_reg==0)); // frame with 0x00
  cover property ((s_axis_tvalid && s_axis_tready && &s_axis_tdata)
                  ##[1:$] (prescale_reg==0 && bit_cnt==0 && busy_reg==0)); // frame with 0xFF
  cover property ((s_axis_tvalid && s_axis_tready)
                  ##[1:$] (prescale_reg==0 && bit_cnt==0 && s_axis_tready_reg && !busy_reg)
                  ##1 (s_axis_tvalid && s_axis_tready)); // back-to-back frames
  cover property ((prescale_reg==0 && bit_cnt>1 && $past(data_reg[0])==1'b0)
                  or (prescale_reg==0 && bit_cnt>1 && $past(data_reg[0])==1'b1)); // shift both bit values

endmodule

// Bind into DUT
bind uart_tx uart_tx_sva #(.DATA_WIDTH(DATA_WIDTH)) uart_tx_sva_i (
  .clk(clk),
  .rst(rst),
  .s_axis_tdata(s_axis_tdata),
  .s_axis_tvalid(s_axis_tvalid),
  .s_axis_tready(s_axis_tready),
  .txd(txd),
  .busy(busy),
  .prescale(prescale),
  .s_axis_tready_reg(s_axis_tready_reg),
  .txd_reg(txd_reg),
  .busy_reg(busy_reg),
  .data_reg(data_reg),
  .prescale_reg(prescale_reg),
  .bit_cnt(bit_cnt)
);