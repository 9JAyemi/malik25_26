// SVA for aur1_STANDARD_CC_MODULE
// Bind these assertions to the DUT
bind aur1_STANDARD_CC_MODULE aur1_STANDARD_CC_MODULE_sva sva();

module aur1_STANDARD_CC_MODULE_sva;

  // local past-valid guard
  bit past_valid;
  always @(posedge USER_CLK) past_valid <= 1'b1;

  // Sanity/no-X
  assert property (@(posedge USER_CLK) !RESET |-> !$isunknown({WARN_CC,DO_CC,enable_cc_c,inner_count_done_r,middle_count_done_c,cc_idle_count_done_c,start_cc_c}));

  // Combinational definitions hold
  assert property (@(posedge USER_CLK) enable_cc_c == !RESET);
  assert property (@(posedge USER_CLK) inner_count_done_r == count_13d_srl_r[11]);
  assert property (@(posedge USER_CLK) middle_count_done_c == (inner_count_done_r && count_16d_srl_r[14]));
  assert property (@(posedge USER_CLK) cc_idle_count_done_c == (middle_count_done_c & count_24d_srl_r[22]));
  assert property (@(posedge USER_CLK) start_cc_c == (prepare_count_r[9] || (enable_cc_c && reset_r)));

  // reset_r is a registered copy of RESET
  assert property (@(posedge USER_CLK) past_valid |-> reset_r == $past(RESET));

  // Synchronous reset effects (next cycle after RESET high)
  assert property (@(posedge USER_CLK)
                   RESET |=> (count_13d_srl_r==12'b0 && count_13d_flop_r==1'b0 &&
                              count_16d_srl_r==15'b0 && count_16d_flop_r==1'b0 &&
                              count_24d_srl_r==23'b0 && count_24d_flop_r==1'b0 &&
                              prepare_count_r==10'b0 && cc_count_r==6'b0 &&
                              WARN_CC==1'b0 && DO_CC==1'b0));

  // 13d SR shift every cycle when not in reset
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   count_13d_srl_r == { $past(count_13d_flop_r), $past(count_13d_srl_r[0:10]) });

  // 13d flop update
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   (enable_cc_c && reset_r) |=> count_13d_flop_r==1'b1);
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   (!(enable_cc_c && reset_r)) |-> (count_13d_flop_r == $past(inner_count_done_r)));

  // 16d SR: conditional shift or hold
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   (inner_count_done_r || !enable_cc_c) |-> 
                     (count_16d_srl_r == { $past(count_16d_flop_r), $past(count_16d_srl_r[0:13]) }));
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   !(inner_count_done_r || !enable_cc_c) |-> (count_16d_srl_r == $past(count_16d_srl_r)));

  // 16d flop priority behavior
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   (enable_cc_c && reset_r) |=> count_16d_flop_r==1'b1);
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   (!(enable_cc_c && reset_r) && inner_count_done_r) |=> (count_16d_flop_r==middle_count_done_c));
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   (!(enable_cc_c && reset_r) && !inner_count_done_r) |-> (count_16d_flop_r==$past(count_16d_flop_r)));

  // 24d SR: conditional shift or hold
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   (middle_count_done_c || !enable_cc_c) |-> 
                     (count_24d_srl_r == { $past(count_24d_flop_r), $past(count_24d_srl_r[0:21]) }));
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   !(middle_count_done_c || !enable_cc_c) |-> (count_24d_srl_r == $past(count_24d_srl_r)));

  // 24d flop priority behavior
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   (enable_cc_c && reset_r) |=> count_24d_flop_r==1'b1);
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   (!(enable_cc_c && reset_r) && middle_count_done_c) |=> (count_24d_flop_r==cc_idle_count_done_c));
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   (!(enable_cc_c && reset_r) && !middle_count_done_c) |-> (count_24d_flop_r==$past(count_24d_flop_r)));

  // prepare_count shift
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   prepare_count_r == {6'd0, $past(cc_idle_count_done_c), $past(prepare_count_r[6:8]) });

  // Latency checks (exact cycle counts, sticky after rise)
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   (enable_cc_c && reset_r) |=> ##13 inner_count_done_r);
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   $rose(inner_count_done_r) |=> ##15 middle_count_done_c);
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   $rose(middle_count_done_c) |=> ##23 cc_idle_count_done_c);

  assert property (@(posedge USER_CLK) disable iff (RESET) $rose(inner_count_done_r) |-> inner_count_done_r[*]);
  assert property (@(posedge USER_CLK) disable iff (RESET) $rose(middle_count_done_c) |-> middle_count_done_c[*]);
  assert property (@(posedge USER_CLK) disable iff (RESET) $rose(cc_idle_count_done_c) |-> cc_idle_count_done_c[*]);

  // WARN_CC behavior
  assert property (@(posedge USER_CLK) RESET |=> !WARN_CC);
  assert property (@(posedge USER_CLK) disable iff (RESET) cc_idle_count_done_c |=> WARN_CC);
  assert property (@(posedge USER_CLK) disable iff (RESET) (!cc_idle_count_done_c && prepare_count_r[9]) |=> !WARN_CC);
  assert property (@(posedge USER_CLK) disable iff (RESET) (!cc_idle_count_done_c && !prepare_count_r[9]) |-> (WARN_CC==$past(WARN_CC)));

  // cc_count shift
  assert property (@(posedge USER_CLK) disable iff (RESET)
                   cc_count_r == { ($past(!enable_cc_c | prepare_count_r[9])), $past(cc_count_r[0:4]) });

  // DO_CC behavior and priority
  assert property (@(posedge USER_CLK) RESET |=> !DO_CC);
  assert property (@(posedge USER_CLK) disable iff (RESET) start_cc_c |=> DO_CC);
  assert property (@(posedge USER_CLK) disable iff (RESET) (!start_cc_c && (cc_count_r!=6'b0)) |=> DO_CC);
  assert property (@(posedge USER_CLK) disable iff (RESET) (!start_cc_c && (cc_count_r==6'b0)) |=> !DO_CC);

  // Coverage: end-to-end bring-up and outputs
  cover property (@(posedge USER_CLK)
                  $fell(RESET) ##13 inner_count_done_r ##15 middle_count_done_c ##23 cc_idle_count_done_c);

  cover property (@(posedge USER_CLK) disable iff (RESET)
                  $rose(cc_idle_count_done_c) ##4 prepare_count_r[9] ##1 WARN_CC);

  cover property (@(posedge USER_CLK) disable iff (RESET)
                  start_cc_c ##1 DO_CC);

endmodule