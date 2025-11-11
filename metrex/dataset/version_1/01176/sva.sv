// SVA checker for serdes_fc_rx
// Bind this module to the DUT to verify internal/external behavior.

module serdes_fc_rx_sva
  #(parameter int LWMARK = 64,
    parameter int HWMARK = 320)
(
  input  logic        clk,
  input  logic        rst,
  input  logic [15:0] fifo_space,
  input  logic        send_xon,
  input  logic        send_xoff,
  input  logic        sent,
  // internal signals (bind to DUT regs)
  input  logic [15:0] countdown,
  input  logic        send_xon_int,
  input  logic        send_xoff_int
);

  // Static configuration checks
  initial begin
    assert (HWMARK > LWMARK)
      else $error("HWMARK (%0d) must be > LWMARK (%0d)", HWMARK, LWMARK);
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Internal request pulses are mutually exclusive per cycle
  assert property (!(send_xon_int && send_xoff_int));

  // XOFF request/transition behavior (at countdown==0 and below low watermark)
  assert property ((countdown==16'd0 && fifo_space < LWMARK)
                   |=> (send_xoff_int && countdown==16'd240));

  // No action when countdown==0 and not below low watermark
  assert property ((countdown==16'd0 && !(fifo_space < LWMARK))
                   |=> (!send_xoff_int && countdown==16'd0));

  // XON request/transition behavior (while counting down and above high watermark)
  assert property ((countdown!=16'd0 && fifo_space > HWMARK)
                   |=> (send_xon_int && countdown==16'd0));

  // Countdown decrements by 1 when active and not cleared by high watermark
  assert property ((countdown!=16'd0 && !(fifo_space > HWMARK))
                   |=> (!send_xon_int && countdown == $past(countdown)-16'd1));

  // Internal request pulses are single-cycle
  assert property (send_xon_int  |-> !$past(send_xon_int));
  assert property (send_xoff_int |-> !$past(send_xoff_int));

  // Countdown never exceeds its programmed max (0 or up to 240)
  assert property (countdown <= 16'd240);

  // Output latch behavior: set one cycle after internal request, clear on sent
  assert property ($past(send_xon_int)  |=> send_xon);
  assert property ($past(send_xoff_int) |=> send_xoff);

  assert property (sent |=> (!send_xon && !send_xoff));

  // Outputs hold value absent a clear or a prior-cycle set request
  assert property ((!sent && !$past(send_xon_int))  |=> send_xon  == $past(send_xon));
  assert property ((!sent && !$past(send_xoff_int)) |=> send_xoff == $past(send_xoff));

  // Basic reset effect (optional, robust to disable iff)
  assert property (@(posedge clk) rst |=> (countdown==16'd0 && !send_xon && !send_xoff));

  // Coverage
  cover property ((countdown==16'd0 && fifo_space < LWMARK) ##1 send_xoff_int);
  cover property ((countdown!=16'd0 && fifo_space > HWMARK) ##1 send_xon_int);
  cover property (send_xoff ##1 sent);
  cover property (send_xon  ##1 sent);
  cover property ((countdown==16'd240) ##1 (countdown==16'd239) ##[1:239] (countdown==16'd0));

endmodule

// Example bind (place in a package or a separate file compiled after the DUT)
// bind serdes_fc_rx serdes_fc_rx_sva #(.LWMARK(LWMARK), .HWMARK(HWMARK)) serdes_fc_rx_sva_i (
//   .clk        (clk),
//   .rst        (rst),
//   .fifo_space (fifo_space),
//   .send_xon   (send_xon),
//   .send_xoff  (send_xoff),
//   .sent       (sent),
//   .countdown      (countdown),
//   .send_xon_int   (send_xon_int),
//   .send_xoff_int  (send_xoff_int)
// );