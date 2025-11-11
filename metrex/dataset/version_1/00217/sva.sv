// SVA for oh_memory_ram
module oh_memory_ram_sva #(parameter DW=104, parameter DEPTH=32, parameter AW=$clog2(DEPTH)) ();
  // Bound inside DUT; direct access to DUT signals and ram[].
  // Past-valid flags to safely use $past
  bit rd_pv, wr_pv;
  always @(posedge rd_clk) rd_pv <= 1'b1;
  always @(posedge wr_clk) wr_pv <= 1'b1;

  // Avoid simultaneous posedges of async clocks (assumption for deterministic sampling)
  assume property (@(posedge wr_clk) ! $rose(rd_clk));
  assume property (@(posedge rd_clk) ! $rose(wr_clk));

  // Address range and no-X checks when enabled
  assert property (@(posedge rd_clk) rd_en |-> (rd_addr < DEPTH) && !$isunknown(rd_addr));
  assert property (@(posedge wr_clk) wr_en |-> (wr_addr < DEPTH) && !$isunknown({wr_addr, wr_wem, wr_din}));
  assert property (@(posedge wr_clk) wr_en |-> !$isunknown(wr_wem));

  // Read path: register holds when rd_en=0; captures RAM when rd_en=1
  assert property (@(posedge rd_clk) disable iff (!rd_pv)
                   !$past(rd_en) |-> rd_dout == $past(rd_dout));
  assert property (@(posedge rd_clk) disable iff (!rd_pv)
                   $past(rd_en) |-> rd_dout == $past(ram[$past(rd_addr)]));

  // Read path: data known after a valid read
  assert property (@(posedge rd_clk) disable iff (!rd_pv)
                   $past(rd_en && (rd_addr < DEPTH) && !$isunknown(rd_addr)) |-> !$isunknown(rd_dout));

  // Write path: masked write semantics on the addressed word
  assert property (@(posedge wr_clk) disable iff (!wr_pv)
                   $past(wr_en) |-> ram[$past(wr_addr)] ==
                     (($past(ram[$past(wr_addr)]) & ~ $past(wr_wem)) |
                      ($past(wr_din) & $past(wr_wem))));

  // No write => addressed word unchanged
  assert property (@(posedge wr_clk) disable iff (!wr_pv)
                   !$past(wr_en) |-> ram[$past(wr_addr)] == $past(ram[$past(wr_addr)]));

  // Coverage: useful scenarios
  cover property (@(posedge wr_clk) wr_en && (wr_wem == '0));                    // zero mask
  cover property (@(posedge wr_clk) wr_en && $onehot(wr_wem));                   // single-bit mask
  cover property (@(posedge wr_clk) wr_en && (wr_wem == {DW{1'b1}}));            // full write
  cover property (@(posedge rd_clk) rd_en && (rd_addr == '0));                   // read addr 0
  cover property (@(posedge rd_clk) rd_en && (rd_addr == DEPTH-1));              // read last addr

  // Cover read-after-write to same address across clocks
  logic [AW-1:0] last_wr_addr;
  always @(posedge wr_clk) if (wr_en && |wr_wem) last_wr_addr <= wr_addr;
  cover property (@(posedge rd_clk) rd_en && (rd_addr == last_wr_addr));
endmodule

bind oh_memory_ram oh_memory_ram_sva #(.DW(DW), .DEPTH(DEPTH), .AW(AW)) ();