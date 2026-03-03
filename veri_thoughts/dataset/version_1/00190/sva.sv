// SVA checker for small_fifo_cntr
module small_fifo_cntr_sva (
  input logic        aclr,
  input logic        clock,
  input logic        cnt_en,
  input logic        updown,
  input logic        sclr,
  input logic [2:0]  q
);

  default clocking cb @(posedge clock); endclocking

  // Basic sanity / knownness
  ASSERT_CTRL_KNOWN: assert property (@cb !$isunknown({aclr,sclr,cnt_en,updown}));
  ASSERT_Q_KNOWN:    assert property (@cb (!aclr) |-> !$isunknown(q));

  // Asynchronous clear: immediate effect and dominance while held
  ASSERT_ACLR_IMM:   assert property (@(posedge aclr) (q == 3'd0 && !$isunknown(q)));
  ASSERT_ACLR_DOM:   assert property (@cb aclr |-> (q == 3'd0));

  // One-cycle next-state functional model (mod-8 up/down, with priorities)
  let exp_next = ( sclr     ? 3'd0
                 : !cnt_en  ? $past(q)
                 :  updown  ? (($past(q)+1) % 8)
                            : (($past(q)+7) % 8) );

  ASSERT_NEXTSTATE: assert property (
    @cb disable iff (aclr || $past(aclr))
      1 |=> (q == exp_next)
  );

  // Coverage
  COVER_ACLR:        cover property (@(posedge aclr) 1);
  COVER_SCLR:        cover property (@cb (!aclr && sclr));
  COVER_UP:          cover property (@cb disable iff (aclr) (!sclr && cnt_en && updown)[*2]);
  COVER_DOWN:        cover property (@cb disable iff (aclr) (!sclr && cnt_en && !updown)[*2]);
  COVER_WRAP_UP:     cover property (@cb disable iff (aclr)
                           ($past(q)==3'd7 && !sclr && cnt_en && updown) |=> (q==3'd0));
  COVER_WRAP_DOWN:   cover property (@cb disable iff (aclr)
                           ($past(q)==3'd0 && !sclr && cnt_en && !updown) |=> (q==3'd7));
  COVER_HOLD:        cover property (@cb disable iff (aclr) (!sclr && !cnt_en && q==$past(q)));

endmodule

bind small_fifo_cntr small_fifo_cntr_sva sva (.*);