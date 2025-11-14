// SVA for pcie_serdes
module pcie_serdes_sva (
  input ref_clk,
  input reset,
  input [31:0] tx_data,
  input tx_valid,
  input tx_ready,
  input rx_valid,
  input [31:0] rx_data,
  input rx_error
);
  default clocking cb @(posedge ref_clk); endclocking

  // Synchronous reset values
  assert property (reset |-> (tx_ready==1'b0 && rx_data==32'b0 && rx_error==1'b0));

  // TX ready next-state truth table (full coverage of 4 input cases)
  assert property (disable iff (reset)  ( tx_valid &&  tx_ready) |=> (!tx_ready)); // handshake consumes ready
  assert property (disable iff (reset)  ( tx_valid && !tx_ready) |=> (!tx_ready)); // stays not-ready while busy
  assert property (disable iff (reset)  (!tx_valid &&  tx_ready) |=> ( tx_ready)); // holds ready when idle
  assert property (disable iff (reset)  (!tx_valid && !tx_ready) |=> ( tx_ready)); // returns to ready when idle+not-ready

  // RX path: shift and tap on valid
  assert property (disable iff (reset)  rx_valid |=> (rx_data[31]==1'b1));                   // MSB inject = rx_valid
  assert property (disable iff (reset)  rx_valid |=> (rx_data[30:0]==$past(rx_data[30:0]))); // lower bits shift
  assert property (disable iff (reset)  rx_valid |=> (rx_error==$past(rx_data[31])));        // tap prior MSB to error
  assert property (disable iff (reset) !rx_valid |=> ($stable(rx_data) && $stable(rx_error)));

  // No X/Z on outputs after reset
  assert property (disable iff (reset) !$isunknown({tx_ready, rx_data, rx_error}));

  // Useful covers
  cover property (disable iff (reset) (tx_valid && tx_ready) ##1 !tx_ready);             // handshake event
  cover property (disable iff (reset) (!tx_valid && !tx_ready) ##1 tx_ready);            // idle raises ready
  cover property (disable iff (reset) rx_valid ##1 (rx_valid && rx_error));              // 2-cycle valid sets rx_error
  cover property (disable iff (reset) tx_ready ##1 (tx_valid && tx_ready) ##1 !tx_ready ##1 (!tx_valid && !tx_ready) ##1 tx_ready);
endmodule

bind pcie_serdes pcie_serdes_sva u_pcie_serdes_sva (.*);