// SVA for byte_swap_pipeline
// Bind this module to the DUT: bind byte_swap_pipeline byte_swap_pipeline_sva sva();

module byte_swap_pipeline_sva;
  // In bound scope, we can directly see: clk, reset, in, out, stage, shift_reg
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Stage value range and transitions
  a_stage_in_range: assert property (stage inside {2'd0,2'd1,2'd2});
  a_s0_to_s1:       assert property (stage==2'd0 |=> stage==2'd1);
  a_s1_to_s2:       assert property (stage==2'd1 |=> stage==2'd2);
  a_s2_to_s0:       assert property (stage==2'd2 |=> stage==2'd0);

  // Reset behavior (synchronous)
  a_reset_sets_s0:  assert property ($rose(reset) |=> stage==2'd0);

  // Combinational stage behaviors (as observed at clock edges)
  a_sr0_load:       assert property (stage==2'd0 |-> shift_reg[0] == in);
  a_sr1_compute:    assert property (stage==2'd1 |-> shift_reg[1] == { $past(in)[23:0],  $past(in)[31:24] });
  a_sr2_compute:    assert property (stage==2'd2 |-> shift_reg[2] == { $past(in,2)[31:24], $past(in,2)[7:0], $past(in,2)[15:8], $past(in,2)[23:16] });

  // Latch-hold expectations across cycles when not active
  a_sr0_hold:       assert property (stage!=2'd0 && $past(stage)!=2'd0 |-> shift_reg[0] == $past(shift_reg[0]));
  a_sr1_hold:       assert property (stage!=2'd1 && $past(stage)!=2'd1 |-> shift_reg[1] == $past(shift_reg[1]));
  a_sr2_hold:       assert property (stage!=2'd2 && $past(stage)!=2'd2 |-> shift_reg[2] == $past(shift_reg[2]));

  // Output gating and timing
  a_out_updates_only_on_s2: assert property ($changed(out) |-> $past(stage)==2'd2);
  a_out_equals_sr2_prev:    assert property ($past(stage)==2'd2 |-> out == $past(shift_reg[2]));

  // End-to-end functional check (3-cycle latency from capture at stage 0)
  a_end_to_end: assert property ($changed(out) |->
                                 out == { $past(in,3)[31:24], $past(in,3)[7:0], $past(in,3)[15:8], $past(in,3)[23:16] });

  // Minimal coverage
  c_one_transaction: cover property (stage==2'd0 ##1 stage==2'd1 ##1 stage==2'd2 ##1 stage==2'd0);
  c_out_event:       cover property ($changed(out));
endmodule