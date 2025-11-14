// SVA checker for hub_core
module hub_core_sva #(parameter int SLAVES = 2,
                      parameter int PCW    = $clog2(SLAVES)+2)
(
  input  logic                   uart_clk,
  input  logic [SLAVES-1:0]      new_nonces,
  input  logic [SLAVES*32-1:0]   slave_nonces,
  input  logic [31:0]            golden_nonce,
  input  logic                   serial_send,
  input  logic                   serial_busy,

  // bind internal DUT regs
  input  logic [SLAVES-1:0]      new_nonces_flag,
  input  logic [PCW-1:0]         port_counter,
  input  logic [SLAVES*32-1:0]   slave_nonces_shifted,
  input  logic [SLAVES-1:0]      clear_nonces
);

  default clocking cb @(posedge uart_clk); endclocking

  bit past_valid;
  always_ff @(posedge uart_clk) past_valid <= 1'b1;
  `define DIS disable iff (!past_valid)

  // Basic sanity (no X on key I/Os)
  assert property (`DIS !$isunknown({serial_busy, new_nonces, slave_nonces}));
  assert property (`DIS !$isunknown({serial_send, golden_nonce}));

  // port_counter: in-range and deterministic modulo-SLAVES increment
  assert property (`DIS port_counter < SLAVES);
  assert property (`DIS port_counter == (($past(port_counter)==SLAVES-1) ? '0 : $past(port_counter)+1));

  // Exact send condition
  assert property (`DIS serial_send == (!serial_busy && new_nonces_flag[port_counter]));

  // clear_nonces next-state behavior
  assert property (`DIS  serial_send |=> clear_nonces[$past(port_counter)]);
  assert property (`DIS !serial_send |=> (clear_nonces == '0));
  assert property (`DIS (clear_nonces != '0) |-> $past(serial_send)); // only set following a send

  // new_nonces_flag state equation
  assert property (`DIS new_nonces_flag == (($past(new_nonces_flag) & ~$past(clear_nonces)) | $past(new_nonces)));

  // Data-path: golden_nonce and shift register behavior
  assert property (`DIS golden_nonce == slave_nonces_shifted[31:0]);
  assert property (`DIS  serial_send |=> slave_nonces_shifted == ($past(slave_nonces) >> ($past(port_counter)*32)));
  assert property (`DIS !serial_send |=> slave_nonces_shifted == $past(slave_nonces_shifted));

  // Busy gating (redundant with exact send condition, but explicit)
  assert property (`DIS serial_busy |-> !serial_send);

  // Coverage
  // 1) Counter wrap
  cover property (`DIS ($past(port_counter)==SLAVES-1) && (port_counter==0));
  // 2) A send observed for each slave index
  genvar i;
  generate
    for (i=0; i<SLAVES; i++) begin : COV_PER_PORT
      cover property (`DIS serial_send && ($past(port_counter)==i));
    end
  endgenerate
  // 3) Back-to-back sends
  cover property (`DIS serial_send ##1 serial_send);
  // 4) Busy suppress then send
  cover property (`DIS (new_nonces_flag[port_counter] && serial_busy)
                        ##1 (!serial_busy) ##[0:SLAVES] serial_send);

  `undef DIS
endmodule

// Bind into DUT
bind hub_core hub_core_sva #(.SLAVES(SLAVES)) u_hub_core_sva (
  .uart_clk(uart_clk),
  .new_nonces(new_nonces),
  .slave_nonces(slave_nonces),
  .golden_nonce(golden_nonce),
  .serial_send(serial_send),
  .serial_busy(serial_busy),
  .new_nonces_flag(new_nonces_flag),
  .port_counter(port_counter),
  .slave_nonces_shifted(slave_nonces_shifted),
  .clear_nonces(clear_nonces)
);