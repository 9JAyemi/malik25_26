// SVA for small_fifo_cntr
module small_fifo_cntr_sva (
  input logic        aclr,
  input logic        clock,
  input logic        cnt_en,
  input logic        updown,
  input logic        sclr,
  input logic [2:0]  q
);

  // Clocking and reset control
  default clocking cb @(posedge clock); endclocking
  default disable iff (aclr);

  // Asynchronous clear: immediate effect and dominance
  a_async_clear_edge:  assert property (@(posedge aclr) q == 3'b000);
  a_async_clear_hold:  assert property (@(posedge clock) aclr |-> q == 3'b000);

  // Synchronous clear has priority over counting
  a_sync_clear:        assert property (sclr |=> q == 3'b000);

  // Hold when disabled (no sclr, no cnt_en)
  a_hold_when_dis:     assert property (!sclr && !cnt_en |=> q == $past(q));

  // Count up/down (mod-8), only when enabled and no sync clear
  a_count_up:          assert property (cnt_en && !sclr &&  updown |=> q == (($past(q)+3'd1) & 3'b111));
  a_count_down:        assert property (cnt_en && !sclr && !updown |=> q == (($past(q)+3'd7) & 3'b111));

  // When enabled without sclr, value must change (mod-8 counter never stalls)
  a_change_when_en:    assert property (cnt_en && !sclr |=> q != $past(q));

  // No X/Z on output
  a_no_xz:             assert property (!$isunknown(q));

  // Coverage: key behaviors
  c_async_clear:       cover  property (@(posedge aclr) q == 3'b000);
  c_sync_clear:        cover  property (sclr ##1 q == 3'b000);
  c_inc_step:          cover  property (!sclr && cnt_en &&  updown && q != 3'd7 |=> q == (($past(q)+3'd1) & 3'b111));
  c_dec_step:          cover  property (!sclr && cnt_en && !updown && q != 3'd0 |=> q == (($past(q)+3'd7) & 3'b111));
  c_wrap_up:           cover  property (!sclr && cnt_en &&  updown && q == 3'd7 |=> q == 3'd0);
  c_wrap_down:         cover  property (!sclr && cnt_en && !updown && q == 3'd0 |=> q == 3'd7);
  c_hold:              cover  property (!sclr && !cnt_en ##1 q == $past(q));

endmodule

// Bind into the DUT (adjust instance path/name as needed)
bind small_fifo_cntr small_fifo_cntr_sva sva (
  .aclr(aclr),
  .clock(clock),
  .cnt_en(cnt_en),
  .updown(updown),
  .sclr(sclr),
  .q(q)
);