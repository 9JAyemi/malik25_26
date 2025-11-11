// SVA for dly01_16
// Bind into DUT to access internal sr
module dly01_16_sva (
  input logic        clk,
  input logic        rst,
  input logic [3:0]  dly,
  input logic        din,
  input logic        dout,
  input logic [15:0] sr
);

  // Basic sanity (no X/Z on key signals)
  ap_no_x_inputs: assert property (@(posedge clk) !$isunknown({rst,dly,din}));
  ap_no_x_state:  assert property (@(posedge clk) !$isunknown({sr,dout}));

  // Shift-register next-state checks
`ifdef SHREG_SEQUENTIAL_RESET
  // Always shift with din & ~rst
  ap_sr_shift: assert property (@(posedge clk)
                                1 |=> sr == { $past(sr[14:0]), $past(din & ~rst) });

  // Holding rst high for 16 cycles flushes sr to zero
  ap_flush_on_rst: assert property (@(posedge clk)
                                    rst[*16] |=> sr == 16'h0000);
`else
  // Synchronous clear on rst, else shift with din
  ap_sr_reset_or_shift: assert property (@(posedge clk)
                                         1 |=> ($past(rst)
                                                ? (sr == 16'h0000)
                                                : (sr == { $past(sr[14:0]), $past(din) })));
`endif

  // Combinational dout function
`ifdef SIMULATION
  ap_dout_all_zero: assert property (@(posedge clk) (sr == 16'h0000) |-> (dout == 1'b0));
  ap_dout_all_one:  assert property (@(posedge clk) (sr == 16'hFFFF) |-> (dout == 1'b1));
  ap_dout_select:   assert property (@(posedge clk) (sr != 16'h0000 && sr != 16'hFFFF)
                                                  |-> (dout == sr[dly]));
`else
  ap_dout_select:   assert property (@(posedge clk) dout == sr[dly]);
`endif

  // Targeted functional covers
  cv_use_dly0:  cover property (@(posedge clk) dly == 4'd0);
  cv_use_dly15: cover property (@(posedge clk) dly == 4'd15);
  cv_all_zero:  cover property (@(posedge clk) sr == 16'h0000);
  cv_all_one:   cover property (@(posedge clk) sr == 16'hFFFF);
  cv_dout_edge: cover property (@(posedge clk) $changed(dout));

endmodule

// Bind into all instances of dly01_16
bind dly01_16 dly01_16_sva sva_i (.*);