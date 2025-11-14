// SVA for serial_tx — bind into DUT scope so internals are visible
module serial_tx_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // State legality
  a_state_legal: assert property (state_q inside {IDLE, START_BIT, DATA, STOP_BIT});

  // Output behavior by state
  a_tx_idle:  assert property (state_q==IDLE     |-> tx==1);
  a_tx_start: assert property (state_q==START_BIT|-> tx==0);
  a_tx_stop:  assert property (state_q==STOP_BIT |-> tx==1);
  a_tx_data:  assert property (state_q==DATA     |-> tx==data_q[bit_ctr_q]);

  // Busy reflects block or non-IDLE
  a_busy_eq: assert property (busy == (block_q || (state_q != IDLE)));
  a_busy_nonidle: assert property ((state_q!=IDLE) |-> busy);

  // IDLE invariants
  a_idle_unblocked: assert property ((state_q==IDLE && !block_q)
                                     |-> (tx==1 && !busy && ctr_q==0 && bit_ctr_q==0));
  a_idle_block_hold: assert property ((state_q==IDLE && block_q)
                                      |=> (state_q==IDLE && tx==1 && busy && $stable(data_q)));
  a_ignore_new_when_blocked: assert property ((state_q==IDLE && block_q && new_data)
                                              |=> (state_q==IDLE && $stable(data_q)));

  // Accept new_data only when unblocked IDLE; latch data and init counters
  a_accept_new: assert property ((state_q==IDLE && !block_q && new_data)
                                 |=> (state_q==START_BIT && ctr_q==0 && bit_ctr_q==0 && busy
                                      && data_q==$past(data)));

  // Start bit length and handoff to DATA
  a_start_len: assert property ($rose(state_q==START_BIT)
                                |-> (state_q==START_BIT && tx==0)[*CLK_PER_BIT]
                                    ##1 (state_q==DATA && ctr_q==0));

  // Counter progression in START/DATA
  a_ctr_inc_sd: assert property (((state_q==START_BIT || state_q==DATA) && ctr_q < (CLK_PER_BIT-1))
                                 |=> (state_q==$past(state_q) && ctr_q==$past(ctr_q)+1));
  a_start_wrap: assert property ((state_q==START_BIT && ctr_q==(CLK_PER_BIT-1))
                                 |=> (state_q==DATA && ctr_q==0));
  a_data_wrap_next: assert property ((state_q==DATA && ctr_q==(CLK_PER_BIT-1) && bit_ctr_q<7)
                                     |=> (state_q==DATA && bit_ctr_q==$past(bit_ctr_q)+1 && ctr_q==0));
  a_data_last_to_stop: assert property ((state_q==DATA && ctr_q==(CLK_PER_BIT-1) && bit_ctr_q==7)
                                        |=> (state_q==STOP_BIT && ctr_q==0));

  // Data register stable outside IDLE (only latched in IDLE)
  a_data_stable_nonidle: assert property ((state_q!=IDLE) |-> $stable(data_q));

  // Stop bit timing and exit to IDLE
  a_stop_inc: assert property ((state_q==STOP_BIT && ctr_q < (CLK_PER_BIT-1))
                               |=> (state_q==STOP_BIT && ctr_q==$past(ctr_q)+1 && tx==1));
  a_stop_to_idle: assert property ((state_q==STOP_BIT && ctr_q==(CLK_PER_BIT-1))
                                   |=> (state_q==IDLE));

  // Coverage
  c_full_tx: cover property ((state_q==IDLE && !block_q && new_data)
                             ##1 state_q==START_BIT
                             ##1 state_q==DATA
                             ##[1:$] (state_q==DATA && bit_ctr_q==7 && ctr_q==(CLK_PER_BIT-1))
                             ##1 state_q==STOP_BIT
                             ##[1:$] (state_q==IDLE && !busy));
  c_data_mixed: cover property (state_q==DATA && tx==0 ##[1:$] state_q==DATA && tx==1);
  c_block_then_send: cover property ((state_q==IDLE && block_q)
                                     ##1 (state_q==IDLE && !block_q && new_data)
                                     ##1 state_q==START_BIT);
endmodule

bind serial_tx serial_tx_sva sva_inst();