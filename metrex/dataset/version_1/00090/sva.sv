// SVA for FIFO_image_filter_gray_data_stream_0_V_shiftReg
// Concise checks for address validity, combinational read, shift/hold semantics, and useful coverage.

`ifndef SYNTHESIS
bind FIFO_image_filter_gray_data_stream_0_V_shiftReg fifo_image_filter_gray_data_stream_0_v_shiftreg_sva sva();

module fifo_image_filter_gray_data_stream_0_v_shiftreg_sva;
  // Bound into DUT scope; can directly reference clk, ce, a, data, q, SRL_SIG, DEPTH, ADDR_WIDTH
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Parameter/address sanity
  initial begin
    assert ((1<<ADDR_WIDTH) >= DEPTH)
      else $error("ADDR_WIDTH too small for DEPTH");
  end
  a_in_range: assert property (a < DEPTH);

  // Combinational read correctness (checked each cycle)
  q_matches_array: assert property (q == SRL_SIG[a]);

  // Shift behavior on ce
  load_0_on_ce: assert property (ce |=> SRL_SIG[0] == $past(data));
  genvar gi;
  generate
    for (gi = 0; gi < DEPTH-1; gi++) begin : g_shift
      shift_chain: assert property (ce |=> SRL_SIG[gi+1] == $past(SRL_SIG[gi]));
    end
  endgenerate

  // Hold behavior when !ce
  hold_0_no_ce: assert property (!ce |=> $stable(SRL_SIG[0]));
  generate
    for (gi = 0; gi < DEPTH-1; gi++) begin : g_hold
      hold_chain_no_ce: assert property (!ce |=> $stable(SRL_SIG[gi+1]));
    end
  endgenerate

  // If address is stable and no shift, q must be stable
  q_stable_when_no_ce_and_addr_stable: assert property (!ce && $stable(a) |=> $stable(q));

  // End-to-end observable behavior (common selects)
  sel0_loads_next: assert property ($past(ce) && $past(a) == '0 |-> q == $past(data));
  sel1_reflects_prev_sel0: assert property ($past(ce) && $past(a) == (DEPTH-1) |-> q == $past(SRL_SIG[0]));

  // Coverage
  cover_ce:              cover property (ce);
  cover_consecutive_ce:  cover property (ce ##1 ce);
  cover_a_lo:            cover property (a == '0);
  cover_a_hi:            cover property (a == (DEPTH-1));
  cover_addr_toggle:     cover property ($changed(a));
endmodule
`endif