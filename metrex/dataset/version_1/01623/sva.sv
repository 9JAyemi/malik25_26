// SVA for rx_dsp_model
// Bind this module to the DUT
module rx_dsp_model_sva();

  // Default clocking
  default clocking cb @(posedge clk); endclocking

  // Track valid past state
  logic past_valid;
  always @(posedge clk) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // Effective decimation (0 => 256)
  function automatic int decim_eff_val(input logic [7:0] d);
    decim_eff_val = (d == 8'h00) ? 256 : d;
  endfunction

  // run_d1 = 1-cycle delayed run
  ap_run_d1_pipe: assert property (disable iff (!past_valid) run_d1 == $past(run));

  // Edge-detect equivalence
  ap_edge1: assert property (disable iff (!past_valid) (run && !run_d1) |-> $rose(run));
  ap_edge2: assert property (disable iff (!past_valid) $rose(run) |-> (run && !run_d1));

  // pktnum behavior
  ap_pkt_inc:  assert property (disable iff (!past_valid || reset) $rose(run) |=> pktnum == $past(pktnum) + 1);
  ap_pkt_hold: assert property (disable iff (!past_valid || reset) ! $rose(run) |=> pktnum == $past(pktnum));

  // counter behavior
  ap_ctr_reset_on_runrise: assert property (disable iff (!past_valid || reset) $rose(run) |=> counter == 16'd0);
  ap_ctr_inc_on_strobe:    assert property (disable iff (!past_valid || reset) (run && strobe && !$rose(run)) |=> counter == $past(counter) + 1);
  ap_ctr_hold_otherwise:   assert property (disable iff (!past_valid || reset) !( $rose(run) || (run && strobe) ) |=> counter == $past(counter));

  // sample behavior
  ap_sample_reset:  assert property (reset |=> sample == 32'h0);
  ap_sample_concat: assert property (disable iff (reset || !past_valid) sample == $past({pktnum, counter}));

  // strobe correctness
  ap_strobe_eq:             assert property (strobe == (stb_ctr == decim - 1));
  ap_strobe_only_when_run:  assert property (strobe |-> run);
  ap_strobe_one_cycle:      assert property ((run && (decim != 8'd1) && $rose(strobe)) |=> !strobe);

  // stb_ctr next-state function
  ap_stb_reset:              assert property (reset |=> stb_ctr == 8'd0);
  ap_stb_on_runrise:         assert property (disable iff (!past_valid || reset) $rose(run) |=> stb_ctr == 8'd1);
  ap_stb_wrap:               assert property (disable iff (!past_valid || reset) (run && (stb_ctr == decim - 1) && !$rose(run)) |=> stb_ctr == 8'd0);
  ap_stb_inc:                assert property (disable iff (!past_valid || reset) (run && !$rose(run) && (stb_ctr != decim - 1)) |=> stb_ctr == $past(stb_ctr) + 1);
  ap_stb_hold_when_run_low:  assert property (disable iff (!past_valid || reset) (!run) |=> stb_ctr == $past(stb_ctr));

  // Periodic strobe when run and decim are stable
  ap_strobe_periodic: assert property (disable iff (!past_valid || reset)
    (run && strobe && $stable(decim))
    |-> (run && !strobe && $stable(decim)) [* (decim_eff_val(decim) - 1)]
        ##1 (run && strobe)
  );

  // Coverage
  cp_run_then_strobe: cover property ($rose(run) ##[1:64] strobe);
  cp_decim_1:         cover property (run && (decim == 8'd1) && strobe);
  cp_decim_0:         cover property (run && (decim == 8'd0) ##[1:260] strobe);
  cp_multi_strobes:   cover property (disable iff (reset) (run && strobe) [*3]);

endmodule

bind rx_dsp_model rx_dsp_model_sva sva_inst();