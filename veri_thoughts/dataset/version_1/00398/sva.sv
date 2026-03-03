// SVA for MISTRAL_FF
module MISTRAL_FF_sva (
  input DATAIN,
  input CLK,
  input ACLR,
  input ENA,
  input SCLR,
  input SLOAD,
  input SDATA,
  input Q
);

  default clocking cb @(posedge CLK); endclocking
  default disable iff (!ACLR);

  // Asynchronous clear behavior
  a_async_clear_now:    assert property (@(negedge ACLR) Q==1'b0);
  a_async_clear_hold:   assert property (@cb !ACLR |-> (Q==1'b0 until_with ACLR));
  a_hold_after_release: assert property (@cb $past(!ACLR) && ACLR |-> (Q==1'b0 until_with ENA));

  // Synchronous priority and functionality (when ENA=1)
  a_sync_pri_clr:   assert property (@cb ENA && SCLR                  |=> Q==1'b0);
  a_sync_pri_load:  assert property (@cb ENA && !SCLR && SLOAD        |=> Q==SDATA);
  a_sync_data_cap:  assert property (@cb ENA && !SCLR && !SLOAD       |=> Q==DATAIN);

  // Hold when disabled
  a_hold_when_dis:  assert property (@cb !ENA                          |=> Q==$past(Q));

  // Change causality: Q changes only on negedge ACLR or posedge CLK with ENA
  a_change_cause:   assert property (@(posedge Q or negedge Q)
                                     ($fell(ACLR) || ($rose(CLK) && ACLR && ENA)));

  // Knownness checks at sampling
  a_no_x_ctrl:      assert property (@cb !$isunknown({ACLR,ENA,SCLR,SLOAD}));
  a_no_x_sdata:     assert property (@cb ENA && !SCLR && SLOAD   |-> !$isunknown(SDATA));
  a_no_x_datain:    assert property (@cb ENA && !SCLR && !SLOAD  |-> !$isunknown(DATAIN));
  a_no_x_q:         assert property (@(posedge CLK or negedge ACLR) !$isunknown(Q));

  // Coverage
  c_async_clear:    cover  property (@(negedge ACLR) Q==1'b0);
  c_release:        cover  property (@cb $past(!ACLR) && ACLR);
  c_sync_clr:       cover  property (@cb ENA && SCLR                  ##1 Q==1'b0);
  c_sync_load:      cover  property (@cb ENA && !SCLR && SLOAD        ##1 Q==SDATA);
  c_sync_data:      cover  property (@cb ENA && !SCLR && !SLOAD       ##1 Q==DATAIN);
  c_hold:           cover  property (@cb !ENA && $stable(Q));
  c_priority_both:  cover  property (@cb ENA && SCLR && SLOAD         ##1 Q==1'b0);

endmodule

bind MISTRAL_FF MISTRAL_FF_sva sva (.*);