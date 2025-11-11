// SVA for profibus_master and profibus_slave
// Bind these to the RTL (no DUT edits required)

bind profibus_master profibus_master_sva();
module profibus_master_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Legal state range
  assert property (tx_state inside {[0:4]});

  // Reset effect (synchronous)
  assert property (reset |=> (tx_state==0 && tx_busy==0));

  // Outputs/sigs sanity (post-reset)
  assert property (!$isunknown(tx_state));
  assert property (!$isunknown(tx_busy));
  assert property (!$isunknown(tx_en));
  // tx_done is used as a handshake; must not be X when evaluated
  assert property ((tx_state inside {[1:4]}) |-> !$isunknown(tx_done));

  // Enable/busy gating
  assert property ((tx_state!=0) |-> (tx_en && tx_busy));
  assert property ((tx_state==0) |-> !tx_en);

  // State advance requires tx_done (1->2->3->4->0)
  assert property ((tx_state==2 && $past(tx_state)==1) |-> $past(tx_done));
  assert property ((tx_state==3 && $past(tx_state)==2) |-> $past(tx_done));
  assert property ((tx_state==4 && $past(tx_state)==3) |-> $past(tx_done));
  assert property ((tx_state==0 && $past(tx_state)==4) |-> $past(tx_done));

  // No skipping states
  assert property (($changed(tx_state)) |-> ((tx_state==$past(tx_state)+1) || (tx_state==0 && $past(tx_state)==4)));

  // Busy behavior around idle/active
  assert property (($rose(tx_busy) && $past(tx_state)==0) |=> (tx_state==1));
  assert property ((tx_state==0 && $past(tx_state)==4) |-> !tx_busy);
  // Auto-retrigger in idle per RTL
  assert property ((tx_state==0 && !tx_busy) |=> tx_busy);

  // Coverage: one full transmit cycle and auto-retrigger
  cover property ($rose(tx_busy)
                  ##[1:$] (tx_state==1) ##1 (tx_state==2) ##1 (tx_state==3) ##1 (tx_state==4) ##1 (tx_state==0 && !tx_busy));
  cover property ((tx_state==0 && !tx_busy) ##1 tx_busy ##1 tx_state==1);
endmodule


bind profibus_slave profibus_slave_sva();
module profibus_slave_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Legal state range
  assert property (rx_state inside {[0:4]});

  // Reset effect
  assert property (reset |=> (rx_state==0));

  // Outputs/sigs sanity (post-reset)
  assert property (!$isunknown(rx_state));
  assert property (!$isunknown(rx_en));
  assert property (!$isunknown(rx_done));

  // Enable/busy/done definitions
  assert property (rx_busy == (rx_state!=0));
  assert property (rx_done == ((rx_state==4) && (rx_data==FRAME_END)));
  assert property ((rx_state!=0) |-> rx_en);
  assert property ((rx_state==0) |-> !rx_en);

  // State advance requires proper handshakes/data
  assert property ((rx_state==2 && $past(rx_state)==1) |-> ($past(rx_done) && $past(rx_data)==FRAME_START));
  assert property ((rx_state==3 && $past(rx_state)==2) |-> $past(rx_done));
  assert property ((rx_state==4 && $past(rx_state)==3) |-> $past(rx_done));
  assert property ((rx_state==0 && $past(rx_state)==4) |-> ($past(rx_done) && $past(rx_data)==FRAME_END));

  // No skipping states
  assert property (($changed(rx_state)) |-> ((rx_state==$past(rx_state)+1) || (rx_state==0 && $past(rx_state)==4)));

  // Coverage: intended full receive sequence with format bytes
  cover property ((rx_state==0)
                  ##1 (rx_state==1)
                  ##1 (rx_state==2 && $past(rx_done) && $past(rx_data)==FRAME_START)
                  ##1 (rx_state==3 && $past(rx_done))
                  ##1 (rx_state==4 && $past(rx_done))
                  ##1 (rx_state==0 && $past(rx_done) && $past(rx_data)==FRAME_END));
endmodule