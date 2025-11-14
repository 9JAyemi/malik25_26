// SVA for dmi_jtag_to_core_sync
// Bind module (non-intrusive)
module dmi_jtag_to_core_sync_sva (
  input clk, input rst_n,
  input rd_en, input wr_en,
  input reg_en, input reg_wr_en,
  input c_rd_en, input c_wr_en,
  input [2:0] rden, input [2:0] wren
);

  // Reset clears state and outputs
  assert property (@(posedge clk)
    !rst_n |-> (rden==3'b0 && wren==3'b0 && !c_rd_en && !c_wr_en && !reg_en && !reg_wr_en)
  );

  // Shift-register behavior
  assert property (@(posedge clk) disable iff (!rst_n)
    $past(rst_n) |-> rden == { $past(rden[1:0]), $past(rd_en) }
  );
  assert property (@(posedge clk) disable iff (!rst_n)
    $past(rst_n) |-> wren == { $past(wren[1:0]), $past(wr_en) }
  );

  // Edge-detect mapping: 1-cycle latency from input rise to pulse
  assert property (@(posedge clk) disable iff (!rst_n)
    $rose(rd_en) |-> ##1 c_rd_en
  );
  assert property (@(posedge clk) disable iff (!rst_n)
    $rose(wr_en) |-> ##1 c_wr_en
  );

  // No spurious pulses: each pulse implies prior 0->1 on input (one cycle earlier)
  assert property (@(posedge clk) disable iff (!rst_n)
    c_rd_en |-> ($past(rd_en) && !$past(rd_en,2))
  );
  assert property (@(posedge clk) disable iff (!rst_n)
    c_wr_en |-> ($past(wr_en) && !$past(wr_en,2))
  );

  // Pulses are single-cycle
  assert property (@(posedge clk) disable iff (!rst_n) c_rd_en |=> !c_rd_en);
  assert property (@(posedge clk) disable iff (!rst_n) c_wr_en |=> !c_wr_en);

  // Output relationships
  assert property (@(posedge clk) disable iff (!rst_n) reg_wr_en == c_wr_en);
  assert property (@(posedge clk) disable iff (!rst_n) reg_en    == (c_wr_en || c_rd_en));

  // Coverage
  cover property (@(posedge clk) !rst_n ##1 rst_n); // reset release
  cover property (@(posedge clk) disable iff (!rst_n) $rose(rd_en) ##1 c_rd_en);
  cover property (@(posedge clk) disable iff (!rst_n) $rose(wr_en) ##1 c_wr_en);
  cover property (@(posedge clk) disable iff (!rst_n)
    $rose(rd_en) && $rose(wr_en) ##1 (c_rd_en && c_wr_en && reg_en && reg_wr_en)
  );
  // back-to-back (minimum spacing) pulses
  cover property (@(posedge clk) disable iff (!rst_n) c_rd_en ##1 !c_rd_en ##1 c_rd_en);
  cover property (@(posedge clk) disable iff (!rst_n) c_wr_en ##1 !c_wr_en ##1 c_wr_en);

endmodule

// Bind into the DUT
bind dmi_jtag_to_core_sync dmi_jtag_to_core_sync_sva sva (
  .clk(clk), .rst_n(rst_n),
  .rd_en(rd_en), .wr_en(wr_en),
  .reg_en(reg_en), .reg_wr_en(reg_wr_en),
  .c_rd_en(c_rd_en), .c_wr_en(c_wr_en),
  .rden(rden), .wren(wren)
);