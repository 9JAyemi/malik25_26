// Bind these assertions into the DUT's scope so SRL_SIG[] is visible.
// Example: bind FIFO_image_filter_dmask_data_stream_0_V_shiftReg FIFO_image_filter_dmask_data_stream_0_V_shiftReg_sva #(.DATA_WIDTH(DATA_WIDTH),.ADDR_WIDTH(ADDR_WIDTH),.DEPTH(DEPTH)) sva();

module FIFO_image_filter_dmask_data_stream_0_V_shiftReg_sva
  #(parameter DATA_WIDTH = 8, parameter ADDR_WIDTH = 1, parameter DEPTH = 2);

  // DUT signals are referenced by name in the bound scope
  // clk, ce, a, data, q, and SRL_SIG[] must exist in the bind target

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  a_known:    assert property (!$isunknown(a));
  ce_known:   assert property (!$isunknown(ce));
  addr_range: assert property (a < DEPTH);

  // Combinational read must reflect selected element
  read_consistent: assert property (q == SRL_SIG[a]);

  // When ce=0, all stages hold their value
  genvar k;
  generate
    for (k = 0; k < DEPTH; k++) begin : g_hold
      hold_no_ce_k: assert property (!ce |=> SRL_SIG[k] == $past(SRL_SIG[k]));
    end
  endgenerate

  // When ce=1, stage 0 loads data and others shift forward one stage
  load_sr0: assert property (ce |=> SRL_SIG[0] == $past(data));
  generate
    if (DEPTH > 1) begin : g_shift
      genvar i;
      for (i = 0; i < DEPTH-1; i++) begin : g_step
        shift_step_i: assert property (ce |=> SRL_SIG[i+1] == $past(SRL_SIG[i]));
      end
    end
  endgenerate

  // End-to-end latency: after j+1 consecutive ce cycles, stage j equals data delayed j+1
  generate
    genvar j;
    for (j = 0; j < DEPTH; j++) begin : g_lat
      lat_j: assert property (ce[* (j+1)] |=> SRL_SIG[j] == $past(data, j+1));
    end
  endgenerate

  // If stalled and address stable, q must be stable
  q_stable_when_stalled: assert property (!ce && $stable(a) |=> $stable(q));

  // Coverage
  cover_ce0: cover property (!ce);
  cover_ce1: cover property (ce);

  generate
    genvar v;
    for (v = 0; v < DEPTH; v++) begin : g_cov_addr
      cover_addr_v: cover property (a == v);
      // Observe delayed data on q when selecting stage v
      cover_delay_to_q_v: cover property (ce[* (v+1)] && a == v ##1 q == $past(data, v+1));
    end
  endgenerate

  cover_stall_then_shift: cover property (!ce ##1 ce);

endmodule