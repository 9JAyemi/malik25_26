// SVA for tx_fct_send
// Bind this module into tx_fct_send:  bind tx_fct_send tx_fct_send_sva();

module tx_fct_send_sva;

  // Access DUT scope symbols via bind (no ports)

  // Local aliases for readability
  localparam int S0 = 3'd0;
  localparam int S1 = 3'd1;
  localparam int S2 = 3'd2;
  localparam int S3 = 3'd3;

  default clocking cb @(posedge pclk_tx); endclocking
  default disable iff (!enable_tx);

  // Basic well-formedness
  assert property (!$isunknown({state_fct_send, next_state_fct_send,
                                state_fct_send_p, next_state_fct_send_p,
                                fct_flag, fct_flag_p, clear_reg_fct_flag,
                                send_null_tx, send_fct_now, fct_sent})));

  // Async reset effect observed on clock
  assert property (!enable_tx |=> (state_fct_send==S0 && fct_flag==3'd0));
  assert property (!enable_tx |=> (state_fct_send_p==S0 && fct_flag_p==3'd0 && clear_reg_fct_flag==1'b0));

  // Gating: when send_null_tx==0, all regs hold
  assert property (send_null_tx==1'b0 |=> $stable({state_fct_send, state_fct_send_p, fct_flag, fct_flag_p, clear_reg_fct_flag}));

  // FSMs load their next_state when gated
  assert property (send_null_tx |-> (state_fct_send    == $past(next_state_fct_send)));
  assert property (send_null_tx |-> (state_fct_send_p  == $past(next_state_fct_send_p)));

  // First FSM next_state consistency (observed behavior)
  assert property (send_null_tx && $past(state_fct_send)==S0 && $past(send_fct_now) |-> state_fct_send==S1);
  assert property (send_null_tx && $past(state_fct_send)==S0 && !$past(send_fct_now) |-> state_fct_send==S0);
  assert property (send_null_tx && $past(state_fct_send)==S1                         |-> state_fct_send==S2);
  assert property (send_null_tx && $past(state_fct_send)==S2 &&  $past(send_fct_now) |-> state_fct_send==S2);
  assert property (send_null_tx && $past(state_fct_send)==S2 && !$past(send_fct_now) |-> state_fct_send==S0);

  // fct_flag update rules
  assert property (send_null_tx && state_fct_send==S1 |-> fct_flag == $past(fct_flag)+3'd1);
  assert property (send_null_tx && state_fct_send==S2 |-> fct_flag == $past(fct_flag));
  assert property (send_null_tx && state_fct_send==S0 && clear_reg_fct_flag |-> fct_flag==3'd0);
  assert property (send_null_tx && state_fct_send==S0 && !clear_reg_fct_flag |-> fct_flag==$past(fct_flag));

  // Second FSM control signal: clear_reg_fct_flag only high in state S2
  assert property (send_null_tx |-> (clear_reg_fct_flag == (state_fct_send_p==S2)));

  // fct_flag_p update rules
  assert property (send_null_tx && state_fct_send_p==S0 |-> (fct_flag_p==3'd7 && clear_reg_fct_flag==1'b0));
  // In S1: load 7 only when fct_flag==7, otherwise hold
  assert property (send_null_tx && state_fct_send_p==S1 && (fct_flag==3'd7) |-> fct_flag_p==3'd7);
  assert property (send_null_tx && state_fct_send_p==S1 && (fct_flag!=3'd7) |-> fct_flag_p==$past(fct_flag_p));
  // In S2: decrement only on fct_sent; and must not underflow
  assert property (send_null_tx && state_fct_send_p==S2 && !fct_sent |-> fct_flag_p==$past(fct_flag_p));
  assert property (send_null_tx && state_fct_send_p==S2 &&  fct_sent |-> (fct_flag_p==$past(fct_flag_p)-3'd1));
  // Safety: don't allow decrement when empty
  assert property (send_null_tx && state_fct_send_p==S2 && fct_sent |-> $past(fct_flag_p)>3'd0);
  // In S3: hold
  assert property (send_null_tx && state_fct_send_p==S3 |-> (fct_flag_p==$past(fct_flag_p) && clear_reg_fct_flag==1'b0));

  // Second FSM observed transitions (key branches)
  assert property (send_null_tx && $past(state_fct_send_p)==S0                       |-> state_fct_send_p==S2);
  assert property (send_null_tx && $past(state_fct_send_p)==S1 && $past(fct_flag)==3'd7 |-> state_fct_send_p==S2);
  assert property (send_null_tx && $past(state_fct_send_p)==S1 && $past(fct_flag)!=3'd7 |-> state_fct_send_p==S1);
  assert property (send_null_tx && $past(state_fct_send_p)==S2 && $past(fct_sent)    |-> state_fct_send_p==S3);
  assert property (send_null_tx && $past(state_fct_send_p)==S2 && !$past(fct_sent)   |-> state_fct_send_p==S2);
  assert property (send_null_tx && $past(state_fct_send_p)==S3 && $past(fct_flag_p)>3'd0 && !$past(fct_sent) |-> state_fct_send_p==S2);
  assert property (send_null_tx && $past(state_fct_send_p)==S3 && $past(fct_flag_p)==3'd0 && !$past(fct_sent)|-> state_fct_send_p==S1);

  // Range/sanity
  assert property (fct_flag inside {[3'd0:3'd7]});
  assert property (fct_flag_p inside {[3'd0:3'd7]});

  // Cross-FSM handshake: when clear asserted and first FSM idle, flag clears next
  assert property (send_null_tx && clear_reg_fct_flag && state_fct_send==S0 |-> fct_flag==3'd0);

  // Coverage
  cover property (disable iff(!enable_tx)
                  send_null_tx ##1 (state_fct_send==S0 && !send_fct_now) ##1
                  (send_fct_now && state_fct_send==S1) ##1 (state_fct_send==S2 && !send_fct_now) ##1 (state_fct_send==S0));

  cover property (disable iff(!enable_tx)
                  send_null_tx && state_fct_send==S1 ##1 send_null_tx && (fct_flag==3'd7));

  cover property (disable iff(!enable_tx)
                  send_null_tx && state_fct_send_p==S0 ##1
                  send_null_tx && state_fct_send_p==S2 ##1
                  send_null_tx && state_fct_send_p==S3 ##1
                  send_null_tx && state_fct_send_p==S2 ##1
                  send_null_tx && state_fct_send_p==S3 ##1
                  send_null_tx && state_fct_send_p==S1);

  cover property (disable iff(!enable_tx)
                  send_null_tx && state_fct_send_p==S2 && fct_sent && (fct_flag_p==3'd1) ##1
                  send_null_tx && state_fct_send_p==S3 ##1
                  send_null_tx && state_fct_send_p==S1);

  // Observe clear event actually zeroes producer count
  cover property (disable iff(!enable_tx)
                  send_null_tx && state_fct_send_p==S2 ##1
                  send_null_tx && clear_reg_fct_flag && state_fct_send==S0 && fct_flag==3'd0);

endmodule

bind tx_fct_send tx_fct_send_sva;