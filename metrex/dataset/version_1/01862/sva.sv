// SVA for uart_rx — bind to DUT to check/cover key behavior concisely.
// Note: rxdata[8] is never written by DUT; data_rx[7] therefore mirrors a stale bit.

module uart_rx_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        rxd,
  input  logic [7:0]  data_rx,
  input  logic        busy,

  // internal DUT signals (bound by name)
  input  logic [8:0]  rxdata,
  input  logic        busy_reg,
  input  logic [9:0]  bitTmr,
  input  logic [3:0]  bitIndex,
  input  logic        rxState,
  input  logic [9:0]  bitCnt_0,
  input  logic [9:0]  bitCnt_1
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Output mapping
  assert property (data_rx == rxdata[8:1]);
  assert property (busy == busy_reg);

  // Reset/idle behavior
  assert property (@cb rst |-> (rxState==1'b0 && busy_reg==1'b0));
  assert property (rxState==1'b0 |-> (bitIndex==4'd0 && bitTmr==10'd0 && bitCnt_0==10'd0 && bitCnt_1==10'd0 && busy_reg==1'b0));

  // Start-bit detect from idle
  assert property (rxState==1'b0 && rxd==1'b0 |=> rxState==1'b1);
  assert property (rxState==1'b0 && rxd==1'b1 |=> rxState==1'b0);

  // bitTmr behavior and range
  assert property (bitTmr <= 10'd7);
  assert property (rxState==1'b1 && bitTmr!=10'd7 |=> bitTmr == $past(bitTmr)+10'd1 && bitIndex==$past(bitIndex));
  assert property (rxState==1'b1 && bitTmr==10'd7 |=> bitTmr==10'd0 && bitCnt_0==10'd0 && bitCnt_1==10'd0);

  // Counters while accumulating within a bit
  assert property (rxState==1'b1 && bitTmr!=10'd7 && rxd==1'b0 |=> bitCnt_0==$past(bitCnt_0)+10'd1 && bitCnt_1==$past(bitCnt_1));
  assert property (rxState==1'b1 && bitTmr!=10'd7 && rxd==1'b1 |=> bitCnt_1==$past(bitCnt_1)+10'd1 && bitCnt_0==$past(bitCnt_0));

  // Majority decision during accumulation affects current bit (uses previous counts)
  assert property (rxState==1'b1 && bitTmr!=10'd7 |=> rxdata[$past(bitIndex)] == (($past(bitCnt_0) > $past(bitCnt_1)) ? 1'b0 : 1'b1));

  // Mid-bit sample and index progression
  assert property (rxState==1'b1 && bitTmr==10'd7 |=> rxdata[$past(bitIndex)] == $past(rxd));
  assert property (rxState==1'b1 && bitTmr==10'd7 && bitIndex!=4'd7 |=> rxState==1'b1 && bitIndex==$past(bitIndex)+4'd1 && busy_reg==1'b1);
  assert property (rxState==1'b1 && bitTmr==10'd7 && bitIndex==4'd7 |=> rxState==1'b0 && busy_reg==1'b0);

  // Busy semantics
  assert property (rxState==1'b0 |-> busy==1'b0);
  assert property (busy==1'b1 |-> rxState==1'b1);

  // Index range while receiving
  assert property (rxState==1'b1 |-> bitIndex<=4'd7);

  // No X on primary outputs when not in reset
  assert property (!$isunknown({busy, data_rx}));

  // Functional coverage

  // Cover a full 8-bit reception: detect start, 8 samples, then idle
  sequence sample_step; rxState && bitTmr==10'd7; endsequence
  cover property (rxState==1'b0 && rxd==1'b0 ##1 rxState==1'b1 ##0 sample_step [->8] ##1 rxState==1'b0);

  // Cover sampling both 0 and 1
  cover property (rxState==1'b1 && bitTmr==10'd7 && rxd==1'b0);
  cover property (rxState==1'b1 && bitTmr==10'd7 && rxd==1'b1);

  // Cover majority-driven interim decisions to 0 and 1
  cover property (rxState==1'b1 && bitTmr!=10'd7 && (bitCnt_0 > bitCnt_1) && rxdata[bitIndex]==1'b0);
  cover property (rxState==1'b1 && bitTmr!=10'd7 && (bitCnt_1 >= bitCnt_0) && rxdata[bitIndex]==1'b1);

endmodule

// Bind into the DUT
bind uart_rx uart_rx_sva u_uart_rx_sva (
  .clk(clk),
  .rst(rst),
  .rxd(rxd),
  .data_rx(data_rx),
  .busy(busy),
  .rxdata(rxdata),
  .busy_reg(busy_reg),
  .bitTmr(bitTmr),
  .bitIndex(bitIndex),
  .rxState(rxState),
  .bitCnt_0(bitCnt_0),
  .bitCnt_1(bitCnt_1)
);