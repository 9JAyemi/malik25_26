// SVA for register_ctrl_top
// Bind this module to the DUT. Focused, high-signal-coverage checks + concise covers.

module register_ctrl_top_sva (
  input  logic         I_sys_clk,
  input  logic         I_sys_rst,

  input  logic         I_usb_uart_tx_full,
  input  logic         I_key_start,

  input  logic         I_usb_uart_rx_empty,
  input  logic [7:0]   I_usb_uart_rx_data,

  output logic         O_usb_uart_tx_req,
  output logic [7:0]   O_usb_uart_tx_data,
  output logic         O_usb_uart_rx_req,
  output logic         O_usb_dir,
  output logic         O_motor_start,
  output logic         tp,

  // internals (for stronger checks)
  input  logic         R_usb_uart_rx_req,
  input  logic         R_usb_uart_rx_req_d1,
  input  logic         R_tx_en,
  input  logic [7:0]   R_tx_data,
  input  logic         R_rx_en,
  input  logic [7:0]   R_rx_data,
  input  logic         R_usb_dir,
  input  logic         R_motor_start
);

  default clocking cb @(posedge I_sys_clk); endclocking
  default disable iff (I_sys_rst);

  // Reset drives known zeros (synchronous reset)
  assert property (disable iff (1'b0) @(posedge I_sys_clk)
                   I_sys_rst |=> (R_usb_uart_rx_req==0 && R_usb_uart_rx_req_d1==0 &&
                                  R_tx_en==0 && R_tx_data==8'h00 &&
                                  R_rx_en==0 && R_rx_data==8'h00 &&
                                  R_usb_dir==0 && R_motor_start==0));

  // Output wiring correctness
  assert property (O_usb_uart_rx_req == R_usb_uart_rx_req);
  assert property (O_usb_uart_tx_req == R_tx_en);
  assert property (O_usb_uart_tx_data == R_tx_data);
  assert property (O_usb_dir         == R_usb_dir);
  assert property (O_motor_start     == R_motor_start);
  assert property (tp == (R_rx_en & (&R_rx_data) & O_motor_start & O_usb_dir));

  // RX request generation and pipeline
  assert property (R_usb_uart_rx_req == (I_usb_uart_rx_empty==1'b0));
  assert property (R_usb_uart_rx_req_d1 == $past(R_usb_uart_rx_req));
  assert property (R_rx_en == R_usb_uart_rx_req_d1);

  // RX data capture only when enabled
  assert property (R_rx_en |-> (R_rx_data == I_usb_uart_rx_data));
  assert property ($changed(R_rx_data) |-> R_rx_en);

  // TX request/data behavior
  assert property (O_usb_uart_tx_req == (!I_usb_uart_tx_full && I_key_start));
  assert property (O_usb_uart_tx_req |-> (O_usb_uart_tx_data == 8'h55));
  assert property (I_usb_uart_tx_full |-> !O_usb_uart_tx_req);

  // Direction control from received command bytes
  assert property ((R_rx_en && (R_rx_data==8'h00)) |-> (O_usb_dir==1'b0));
  assert property ((R_rx_en && (R_rx_data==8'hff)) |-> (O_usb_dir==1'b1));
  assert property ($changed(O_usb_dir) |-> (R_rx_en && ((R_rx_data==8'h00)||(R_rx_data==8'hff))));

  // Motor start control: pulse only with 0x02 when RX enabled; forced low when not enabled
  assert property ((R_rx_en && (R_rx_data==8'h02)) |-> O_motor_start);
  assert property ((!R_rx_en) |-> !O_motor_start);
  assert property ($rose(O_motor_start) |-> (R_rx_en && (R_rx_data==8'h02)));
  assert property ($fell(O_motor_start) |-> (!R_rx_en));

  // Functional coverage (concise)
  cover property (!I_usb_uart_rx_empty ##1 O_usb_uart_rx_req);
  cover property (!I_usb_uart_tx_full && I_key_start && O_usb_uart_tx_req && (O_usb_uart_tx_data==8'h55));
  cover property (R_rx_en && (R_rx_data==8'h00) && (O_usb_dir==0));
  cover property (R_rx_en && (R_rx_data==8'hff) && (O_usb_dir==1));
  cover property (R_rx_en && (R_rx_data==8'h02) && O_motor_start);
  cover property ($rose(O_usb_dir)); // any direction change up
  cover property ($fell(O_usb_dir)); // any direction change down
  cover property (tp);

endmodule

bind register_ctrl_top register_ctrl_top_sva sva (
  .I_sys_clk            (I_sys_clk),
  .I_sys_rst            (I_sys_rst),
  .I_usb_uart_tx_full   (I_usb_uart_tx_full),
  .I_key_start          (I_key_start),
  .I_usb_uart_rx_empty  (I_usb_uart_rx_empty),
  .I_usb_uart_rx_data   (I_usb_uart_rx_data),
  .O_usb_uart_tx_req    (O_usb_uart_tx_req),
  .O_usb_uart_tx_data   (O_usb_uart_tx_data),
  .O_usb_uart_rx_req    (O_usb_uart_rx_req),
  .O_usb_dir            (O_usb_dir),
  .O_motor_start        (O_motor_start),
  .tp                   (tp),
  // internals
  .R_usb_uart_rx_req    (R_usb_uart_rx_req),
  .R_usb_uart_rx_req_d1 (R_usb_uart_rx_req_d1),
  .R_tx_en              (R_tx_en),
  .R_tx_data            (R_tx_data),
  .R_rx_en              (R_rx_en),
  .R_rx_data            (R_rx_data),
  .R_usb_dir            (R_usb_dir),
  .R_motor_start        (R_motor_start)
);