// SVA for pcieInterface
// Focused, concise checks + coverage. Bind into the DUT.

module pcieInterface_sva (
  input logic        sys_clkp,
  input logic        sys_clkn,
  input logic        pci_clkp,
  input logic        pci_clkn,
  input logic        pci_reset_n,
  input logic [7:0]  pci_rxp,
  input logic [7:0]  pci_rxn,
  input logic        pps_in,
  input logic [7:0]  pci_txp,
  input logic [7:0]  pci_txn,
  input logic [2:0]  led,
  input logic        pps_out
);

  // Differential clock sanity (environment)
  assert property (@(posedge sys_clkp) sys_clkn == ~sys_clkp)
    else $error("sys_clkn not inverse of sys_clkp");

  assert property (@(posedge pci_clkp) pci_clkn == ~pci_clkp)
    else $error("pci_clkn not inverse of pci_clkp");

  // Reset behavior (next cycle low = zeroed outputs)
  assert property (@(posedge pci_clkp) !pci_reset_n |=> (pci_txp == 8'h00 && pci_txn == 8'h00 && led == 3'h0))
    else $error("Outputs not cleared after reset asserted");

  // Hold zeros while reset stays low
  assert property (@(posedge pci_clkp) (!pci_reset_n && $past(!pci_reset_n)) |-> (pci_txp == 8'h00 && pci_txn == 8'h00 && led == 3'h0 && $stable({pci_txp,pci_txn,led})))
    else $error("Outputs not held at zero during reset");

  // PCIe TX mirrors RX (1-cycle latency when out of reset)
  assert property (@(posedge pci_clkp) pci_reset_n |=> (pci_txp == $past(pci_rxp) && pci_txn == $past(pci_rxn)))
    else $error("TX != past RX");

  // LED mirrors low 3 bits of RX (1-cycle latency)
  assert property (@(posedge pci_clkp) pci_reset_n |=> (led == $past(pci_rxp[2:0])))
    else $error("LED != past RX[2:0]");

  // No X/Z on outputs when out of reset
  assert property (@(posedge pci_clkp) pci_reset_n |-> !$isunknown({pci_txp,pci_txn,led}))
    else $error("Unknown on outputs with reset deasserted");

  // PPS sync (1-cycle latency to sys_clkp domain)
  assert property (@(posedge sys_clkp) 1'b1 |=> (pps_out == $past(pps_in)))
    else $error("pps_out != past pps_in");

  // PPS only changes if pps_in changed on previous sys_clkp
  assert property (@(posedge sys_clkp) $changed(pps_out) |-> $past($changed(pps_in)))
    else $error("pps_out changed without prior pps_in change");

  // --------------- Coverage ---------------

  // Reset pulse and recovery
  cover property (@(posedge pci_clkp) !pci_reset_n ##1 $rose(pci_reset_n));

  // Observe pass-through on a data change
  cover property (@(posedge pci_clkp) pci_reset_n && $changed(pci_rxp) ##1 (pci_txp == $past(pci_rxp)));

  // Exercise all LED codes
  genvar i;
  generate for (i = 0; i < 8; i++) begin : C_LED
    cover property (@(posedge pci_clkp) pci_reset_n ##1 (led == i[2:0] && $past(pci_rxp[2:0]) == i[2:0]));
  end endgenerate

  // PPS toggle observed across the synchronizer
  cover property (@(posedge sys_clkp) $changed(pps_in) ##1 (pps_out == $past(pps_in)));

endmodule

// Bind into DUT
bind pcieInterface pcieInterface_sva u_pcieInterface_sva (
  .sys_clkp(sys_clkp),
  .sys_clkn(sys_clkn),
  .pci_clkp(pci_clkp),
  .pci_clkn(pci_clkn),
  .pci_reset_n(pci_reset_n),
  .pci_rxp(pci_rxp),
  .pci_rxn(pci_rxn),
  .pps_in(pps_in),
  .pci_txp(pci_txp),
  .pci_txn(pci_txn),
  .led(led),
  .pps_out(pps_out)
);