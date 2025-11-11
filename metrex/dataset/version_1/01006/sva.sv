// SVA for counter_3bit
module counter_3bit_sva (
  input logic        clk,
  input logic        reset,
  input logic        inc_dec,
  input logic [2:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // X/Z checks at sampling edges
  ap_no_x:            assert property (!$isunknown({reset, inc_dec, count}));

  // Asynchronous reset: immediate set to 0 and hold while asserted
  ap_async_set0:      assert property (@(posedge reset) ##0 (count == 3'd0));
  ap_hold_during_rst: assert property (reset |-> (count == 3'd0));

  // Counter must change every active clock edge (no hold state)
  ap_always_moves:    assert property (disable iff (reset) count != $past(count));

  // Up-count behavior with wrap
  ap_step_up:         assert property (disable iff (reset)
                                       inc_dec |=> count == (($past(count)==3'd7) ? 3'd0 : $past(count)+3'd1));

  // Down-count behavior with wrap
  ap_step_dn:         assert property (disable iff (reset)
                                       !inc_dec |=> count == (($past(count)==3'd0) ? 3'd7 : $past(count)-3'd1));

  // Coverage: observe both wrap events
  cp_wrap_up:         cover  property (disable iff (reset)
                                       inc_dec && ($past(count)==3'd7) |=> (count==3'd0));
  cp_wrap_dn:         cover  property (disable iff (reset)
                                       !inc_dec && ($past(count)==3'd0) |=> (count==3'd7));

  // Coverage: hit all 8 states
  generate
    genvar i;
    for (i=0; i<8; i++) begin : g_state_cov
      cp_state: cover property (disable iff (reset) count == i[2:0]);
    end
  endgenerate

endmodule

bind counter_3bit counter_3bit_sva sva_i (
  .clk    (clk),
  .reset  (reset),
  .inc_dec(inc_dec),
  .count  (count)
);