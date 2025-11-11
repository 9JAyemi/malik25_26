// SVA for module test
// Bind this file to the DUT: bind test test_sva();

`ifndef ASSERT_OFF
module test_sva;

  // Default: disable assertions while reset=1
  // (Use explicit reset-edge properties for reset values)
  // NOTE: All properties directly reference DUT scope via bind.
  // Clocks: use CLK for counter/good relation; use good for game logic.

  // ------------- Counter/good/outs -------------
  ap_out_reset: assert property (@(posedge CLK) reset |-> out==23'd0);
  ap_out_inc:   assert property (@(posedge CLK) disable iff (reset) out == $past(out)+23'd1);
  ap_good_def:  assert property (@(posedge CLK) good == (out==23'd100000));

  ap_outs_rst:  assert property (@(posedge reset) outs==1'b0);
  ap_outs_tgl:  assert property (@(posedge good) disable iff (reset) outs != $past(outs));
  ap_outs_stable: assert property (@(posedge CLK) disable iff (reset) !$rose(good) |-> $stable(outs));

  // No X on primary outputs (sampled on CLK domain)
  ap_no_x: assert property (@(posedge CLK) disable iff (reset)
                            !$isunknown({outs,win,lose,equal,bigger,smaller,nums,numa}));

  // ------------- Modes and bounds (good domain) -------------
  ap_runa_runb_mutex: assert property (@(posedge good) disable iff (reset) !(runa && runb));
  ap_numa_bound:      assert property (@(posedge good) disable iff (reset) (numa <= 4'd7));
  ap_numb_bound:      assert property (@(posedge good) disable iff (reset) (numb <= 4'd7));

  ap_runa_to_runb_numa7: assert property (@(posedge good) disable iff (reset)
                                          (numa==4'd7) |-> (runa==1'b0 && runb==1'b1));
  ap_runa_to_runb_enter: assert property (@(posedge good) disable iff (reset)
                                          (enter && !ins[4] && (numa>4'd3))
                                          |-> (runa==1'b0 && runb==1'b1));
  ap_runb_stop_numb7:    assert property (@(posedge good) disable iff (reset)
                                          (numb==4'd7) |-> (runb==1'b0));

  // ------------- ins[] edge gating (good domain) -------------
  ap_ins0_set: assert property (@(posedge good) disable iff (reset) (I1 && !ins[0]) |-> ins[0]);
  ap_ins0_clr: assert property (@(posedge good) disable iff (reset) (!I1) |-> !ins[0]);
  ap_ins1_set: assert property (@(posedge good) disable iff (reset) (I2 && !ins[1]) |-> ins[1]); // BUG catcher
  ap_ins1_clr: assert property (@(posedge good) disable iff (reset) (!I2) |-> !ins[1]);
  ap_ins2_set: assert property (@(posedge good) disable iff (reset) (I3 && !ins[2]) |-> ins[2]);
  ap_ins2_clr: assert property (@(posedge good) disable iff (reset) (!I3) |-> !ins[2]);
  ap_ins3_set: assert property (@(posedge good) disable iff (reset) (I4 && !ins[3]) |-> ins[3]);
  ap_ins3_clr: assert property (@(posedge good) disable iff (reset) (!I4) |-> !ins[3]);
  ap_ins4_set: assert property (@(posedge good) disable iff (reset) (enter && !ins[4]) |-> ins[4]); // BUG catcher
  ap_ins4_clr: assert property (@(posedge good) disable iff (reset) (!enter) |-> !ins[4]);

  // ------------- nums one-hot on key press -------------
  ap_nums_I1: assert property (@(posedge good) disable iff (reset) (I1 && !ins[0]) |-> nums==4'b0001);
  ap_nums_I2: assert property (@(posedge good) disable iff (reset) (I2 && !ins[1]) |-> nums==4'b0010);
  ap_nums_I3: assert property (@(posedge good) disable iff (reset) (I3 && !ins[2]) |-> nums==4'b0100);
  ap_nums_I4: assert property (@(posedge good) disable iff (reset) (I4 && !ins[3]) |-> nums==4'b1000);

  // ------------- Counters monotonicity -------------
  ap_numa_monotonic: assert property (@(posedge good) disable iff (reset) $past(numa) <= numa);
  ap_numb_monotonic: assert property (@(posedge good) disable iff (reset) $past(numb) <= numb);
  ap_numa_stable_no_press: assert property (@(posedge good) disable iff (reset)
     runa && !(I1 && !ins[0]) && !(I2 && !ins[1]) && !(I3 && !ins[2]) && !(I4 && !ins[3]) |-> $stable(numa));
  ap_numb_stable_no_press: assert property (@(posedge good) disable iff (reset)
     runb && !(I1 && !ins[0]) && !(I2 && !ins[1]) && !(I3 && !ins[2]) && !(I4 && !ins[3]) |-> $stable(numb));

  // Helper: exactly one key press (good domain)
  function automatic bit one_press;
    return ( (I1 && !ins[0]) + (I2 && !ins[1]) + (I3 && !ins[2]) + (I4 && !ins[3]) ) == 1;
  endfunction

  // Single-press effects
  ap_runa_inc_one: assert property (@(posedge good) disable iff (reset) runa && one_press() |-> (numa == $past(numa)+1));
  ap_runb_inc_one: assert property (@(posedge good) disable iff (reset) runb && one_press() |-> (numb == $past(numb)+1));
  ap_write_a1: assert property (@(posedge good) disable iff (reset) runa && one_press() && (I1 && !ins[0]) |-> a1[$past(numa)]);
  ap_write_a2: assert property (@(posedge good) disable iff (reset) runa && one_press() && (I2 && !ins[1]) |-> a2[$past(numa)]);
  ap_write_a3: assert property (@(posedge good) disable iff (reset) runa && one_press() && (I3 && !ins[2]) |-> a3[$past(numa)]);
  ap_write_a4: assert property (@(posedge good) disable iff (reset) runa && one_press() && (I4 && !ins[3]) |-> a4[$past(numa)]);
  ap_write_b1: assert property (@(posedge good) disable iff (reset) runb && one_press() && (I1 && !ins[0]) |-> b1[$past(numb)]);
  ap_write_b2: assert property (@(posedge good) disable iff (reset) runb && one_press() && (I2 && !ins[1]) |-> b2[$past(numb)]);
  ap_write_b3: assert property (@(posedge good) disable iff (reset) runb && one_press() && (I3 && !ins[2]) |-> b3[$past(numb)]);
  ap_write_b4: assert property (@(posedge good) disable iff (reset) runb && one_press() && (I4 && !ins[3]) |-> b4[$past(numb)]);

  // ------------- Enter/comparison flow -------------
  ap_enter_short_resets: assert property (@(posedge good) disable iff (reset)
    (enter && !ins[4] && (numa < 4))
    |-> (a1==7'b0 && a2==7'b0 && a3==7'b0 && a4==7'b0 && numa==4'd0));

  ap_compare_compute: assert property (@(posedge good) disable iff (reset)
    (enter && !ins[4] && $past(numb) >= 4)
    |-> (suc == ((a1~^b1)&(a2~^b2)&(a3~^b3)&(a4~^b4)) && win == &suc));

  ap_turn_and_clear: assert property (@(posedge good) disable iff (reset)
    (enter && !ins[4] && $past(numb) >= 4 && !win && ($past(turn) < 4))
    |-> (turn == $past(turn)+1 && b1==7'b0 && b2==7'b0 && b3==7'b0 && b4==7'b0));

  ap_set_lose: assert property (@(posedge good) disable iff (reset)
    (enter && !ins[4] && !win && ($past(turn) >= 4'd3)) |-> lose);

  ap_numb_zero_after_compare: assert property (@(posedge good) disable iff (reset)
    (enter && !ins[4] && $past(numb) >= 4) |-> (numb==4'd0));

  // Flags correctness and exclusivity
  ap_flags_excl: assert property (@(posedge good) disable iff (reset)
    !(equal && bigger) && !(equal && smaller) && !(bigger && smaller));

  ap_flags_cmp: assert property (@(posedge good) disable iff (reset)
    (enter && !ins[4] && $past(numb) >= 4)
    |-> ( equal  == ($past(numb)==$past(numa))
       && bigger == ($past(numb)< $past(numa))
       && smaller== ($past(numb)> $past(numa)) ));

  // ------------- Coverage -------------
  cp_outs_toggle: cover property (@(posedge good) !reset ##1 outs);
  cp_press_each:  cover property (@(posedge good)
                     (I1 && !ins[0]) ##1 (I2 && !ins[1]) ##1 (I3 && !ins[2]) ##1 (I4 && !ins[3]));
  cp_to_runb:     cover property (@(posedge good) (numa>3) ##0 (enter && !ins[4]) ##0 runb);
  cp_win:         cover property (@(posedge good) (enter && !ins[4] && $past(numb)>=4 && win));
  cp_lose:        cover property (@(posedge good) (enter && !ins[4] && !win && ($past(turn)>=3) && lose));

endmodule
`endif