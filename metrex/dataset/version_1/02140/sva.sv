// SVA for tx_reset_sm
module tx_reset_sm_sva
(
  input refclkdiv2,
  input rst_n,
  input tx_pll_lol_qd_s,
  input tx_pcs_rst_ch_c,
  input rst_qd_c
);

  default clocking cb @ (posedge refclkdiv2); endclocking
  default disable iff (!rst_n);

  // Elaboration-time parameter sanity
  initial begin
    assert (count_index < TIMER2WIDTH)
      else $error("count_index must be < TIMER2WIDTH");
  end

  // No X on key signals
  assert property (!$isunknown({cs,ns,tx_pcs_rst_ch_c,rst_qd_c,TIMER1,TIMER2})));

  // Legal state encoding
  assert property (cs inside {QUAD_RESET,WAIT_FOR_TIMER1,CHECK_PLOL,WAIT_FOR_TIMER2,NORMAL});

  // cs follows ns
  assert property ($past(rst_n) |-> cs == $past(ns));

  // Asynchronous reset behavior
  assert property (!rst_n |-> cs==QUAD_RESET && tx_pll_lol_qd_s_int==1 && tx_pll_lol_qd_s_int1==1
                              && tx_pcs_rst_ch_c==1 && rst_qd_c==1);

  // State-driven internal outputs
  assert property ( (cs==QUAD_RESET)      |-> (tx_pcs_rst_ch_c_int==4'hF && rst_qd_c_int==1) );
  assert property ( (cs==WAIT_FOR_TIMER1) |-> (tx_pcs_rst_ch_c_int==4'hF && rst_qd_c_int==1) );
  assert property ( (cs==CHECK_PLOL)      |-> (tx_pcs_rst_ch_c_int==4'hF && rst_qd_c_int==0) );
  assert property ( (cs==WAIT_FOR_TIMER2) |-> (tx_pcs_rst_ch_c_int==4'hF && rst_qd_c_int==0) );
  assert property ( (cs==NORMAL)          |-> (tx_pcs_rst_ch_c_int==4'h0 && rst_qd_c_int==0) );

  // Registered outputs match internal controls
  assert property (tx_pcs_rst_ch_c == tx_pcs_rst_ch_c_int[0]);
  assert property (rst_qd_c == rst_qd_c_int);

  // Reset timer strobes only in their states
  assert property (reset_timer1 == (cs==QUAD_RESET));
  assert property (reset_timer2 == (cs==CHECK_PLOL));

  // Next-state function correctness
  assert property ( (cs==QUAD_RESET) |-> (ns==WAIT_FOR_TIMER1 && reset_timer1) );
  assert property ( (cs==WAIT_FOR_TIMER1) |-> (ns == (TIMER1 ? CHECK_PLOL : WAIT_FOR_TIMER1)) );
  assert property ( (cs==CHECK_PLOL) |-> (ns==WAIT_FOR_TIMER2 && reset_timer2) );
  assert property ( (cs==WAIT_FOR_TIMER2 && !TIMER2) |-> (ns==WAIT_FOR_TIMER2) );
  assert property ( (cs==WAIT_FOR_TIMER2 && TIMER2 && tx_pll_lol_qd_s_int)  |-> (ns==QUAD_RESET) );
  assert property ( (cs==WAIT_FOR_TIMER2 && TIMER2 && !tx_pll_lol_qd_s_int) |-> (ns==NORMAL) );
  assert property ( (cs==NORMAL) |-> (ns == (tx_pll_lol_qd_s_int ? QUAD_RESET : NORMAL)) );

  // Outputs consistent with state (registered)
  assert property ( (cs inside {QUAD_RESET,WAIT_FOR_TIMER1,CHECK_PLOL,WAIT_FOR_TIMER2}) |-> tx_pcs_rst_ch_c==1 );
  assert property ( (cs==NORMAL) |-> tx_pcs_rst_ch_c==0 );
  assert property ( (cs inside {QUAD_RESET,WAIT_FOR_TIMER1}) |-> rst_qd_c==1 );
  assert property ( (cs inside {CHECK_PLOL,WAIT_FOR_TIMER2,NORMAL}) |-> rst_qd_c==0 );

  // Synchronizer correctness (allow 2-cycle history)
  assert property (rst_n && $past(rst_n,2) |-> tx_pll_lol_qd_s_int1 == $past(tx_pll_lol_qd_s,1));
  assert property (rst_n && $past(rst_n,2) |-> tx_pll_lol_qd_s_int  == $past(tx_pll_lol_qd_s,2));

  // TIMER1 behavior
  assert property (reset_timer1 |-> (counter1==0 && TIMER1==0));
  assert property (TIMER1 == counter1[2]);
  assert property ($past(rst_n) && !$past(reset_timer1) && !$past(counter1[2]) |-> counter1 == $past(counter1)+1);
  assert property ($rose(TIMER1) |-> TIMER1 until reset_timer1);

  // TIMER2 behavior
  assert property (reset_timer2 |-> (counter2==0 && TIMER2==0));
  assert property (TIMER2 == counter2[count_index]);
  assert property ($past(rst_n) && !$past(reset_timer2) && !$past(counter2[count_index]) |-> counter2 == $past(counter2)+1);
  assert property ($rose(TIMER2) |-> TIMER2 until reset_timer2);

  // Transition guards require timers
  assert property ((cs==WAIT_FOR_TIMER1 && ns==CHECK_PLOL) |-> TIMER1);
  assert property ((cs==WAIT_FOR_TIMER2 && ns!=WAIT_FOR_TIMER2) |-> TIMER2);

  // Coverage
  cover property (cs==QUAD_RESET ##1 cs==WAIT_FOR_TIMER1 ##[1:$] cs==CHECK_PLOL ##1 cs==WAIT_FOR_TIMER2 ##[1:$] cs==NORMAL);
  cover property (cs==NORMAL && tx_pll_lol_qd_s_int ##1 cs==QUAD_RESET);
  cover property (cs==WAIT_FOR_TIMER2 && TIMER2 && !tx_pll_lol_qd_s_int ##1 cs==NORMAL);
  cover property (cs==WAIT_FOR_TIMER2 && TIMER2 && tx_pll_lol_qd_s_int  ##1 cs==QUAD_RESET);

endmodule

bind tx_reset_sm tx_reset_sm_sva sva(.refclkdiv2(refclkdiv2),
                                     .rst_n(rst_n),
                                     .tx_pll_lol_qd_s(tx_pll_lol_qd_s),
                                     .tx_pcs_rst_ch_c(tx_pcs_rst_ch_c),
                                     .rst_qd_c(rst_qd_c));