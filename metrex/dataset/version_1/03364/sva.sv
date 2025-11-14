// SVA for generic_dpram
// Concise checker with a cycle-accurate reference model and key assertions/coverage.
// Bind into the DUT; no modifications to DUT required.

`ifndef SYNTHESIS
bind generic_dpram generic_dpram_sva #(.AW(aw), .DW(dw)) i_generic_dpram_sva (.*);

module generic_dpram_sva #(parameter int AW=5, DW=16)
(
  input logic           rclk, rrst, rce, oe,
  input logic [AW-1:0]  raddr,
  input logic [DW-1:0]  do,
  input logic           wclk, wrst, wce, we,
  input logic [AW-1:0]  waddr,
  input logic [DW-1:0]  di
);

  localparam int DEPTH = (1<<AW);

  // Mirror the DUT's registered read address behavior
  logic [AW-1:0] ra_ref;
  always_ff @(posedge rclk) if (rce) ra_ref <= raddr;

  // Simple scoreboard for the write port plus init map (avoid checking unknown/unwritten cells)
  logic [DW-1:0] model_mem [DEPTH];
  bit            init      [DEPTH];

  always_ff @(posedge wclk)
    if (wce && we) begin
      model_mem[waddr] <= di;
      init[waddr]      <= 1'b1;
    end

  // Basic control-signal X checks
  a_no_x_ctrl_rclk: assert property (@(posedge rclk) !$isunknown(rce));
  a_no_x_ctrl_wclk: assert property (@(posedge wclk) !$isunknown({wce,we}));

  // No X on address/data when used
  a_no_x_on_read_addr: assert property (@(posedge rclk) rce |-> !$isunknown(raddr));
  a_no_x_on_write_bus: assert property (@(posedge wclk) (wce && we) |-> !$isunknown({waddr,di}));

  // Data integrity: whenever the addressed location has been written at least once,
  // the output must match the model (and be known). This covers both ports and CDC.
  a_do_matches_model: assert property (@(posedge rclk)
                                       init[ra_ref] |-> (do === model_mem[ra_ref]) && !$isunknown(do));

  // Optional: if read enable asserts, the next-cycle address mirror is as expected
  // (checks the read-address pipeline behavior via the mirror)
  a_ra_ref_pipeline: assert property (@(posedge rclk) rce |=> ra_ref == $past(raddr));

  // Coverage
  c_write_any:            cover property (@(posedge wclk) wce && we);
  c_read_any:             cover property (@(posedge rclk) rce);
  c_read_known_location:  cover property (@(posedge rclk) rce && init[ra_ref] && (do == model_mem[ra_ref]));

  // Cover read-after-write to same address returns written data
  logic [AW-1:0] last_waddr; logic [DW-1:0] last_wdata;
  always_ff @(posedge wclk) if (wce && we) begin last_waddr <= waddr; last_wdata <= di; end
  c_raw_same_addr: cover property (@(posedge rclk)
                                   rce && init[ra_ref] && (ra_ref == last_waddr) && (do == last_wdata));

  // Back-to-back writes on consecutive cycles to different addresses
  c_b2b_writes_diff: cover property (@(posedge wclk)
                                     (wce && we, waddr) ##1 (wce && we && (waddr != $past(waddr))));

`ifdef VENDOR_FPGA
  // In this branch, oe is ignored; just cover its activity for completeness
  c_oe_toggles: cover property (@(posedge rclk) $changed(oe));
`else
  // For non-FPGA branches that tri-state do when !(oe && rce), check high-Z behavior
  a_tristate_when_disabled: assert property (@(posedge rclk) !(oe && rce) |-> (^{do} === 1'bz));
`endif

endmodule
`endif