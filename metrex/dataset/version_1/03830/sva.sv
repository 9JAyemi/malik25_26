// SVA for vending_machine_fsm
module vending_machine_fsm_sva;

  default clocking cb @(posedge clk); endclocking

  // track past-valid for safe $past use
  logic past_valid;
  always_ff @(posedge clk) if (reset) past_valid <= 1'b0; else past_valid <= 1'b1;

  // Basic sanity
  a_no_x_state:        assert property (!$isunknown(state));
  a_state_legal:       assert property (state inside {IDLE, WAITING_FOR_COINS, DISPENSING});
  a_no_x_next_state:   assert property (!$isunknown(next_state));
  a_no_x_regs:         assert property (!$isunknown({coins_inserted,display_output,product_output}));
  a_price_const:       assert property ($stable(price) && price==4'b0010);

  // Reset behavior
  a_reset_vals:        assert property (reset |=> state==IDLE && coins_inserted==0 && display_output==price && product_output==0);
  a_idle_after_reset:  assert property (disable iff (reset) $fell(reset) |=> state==IDLE);

  // Next-state function correctness (combinational intent)
  a_next_state_idle:   assert property (state==IDLE |-> next_state==(coin_input ? WAITING_FOR_COINS : IDLE));
  a_next_state_wait:   assert property (state==WAITING_FOR_COINS |-> next_state==(coin_input ? WAITING_FOR_COINS
                                                           : ((button_input && coins_inserted>=price) ? DISPENSING
                                                                                                      : WAITING_FOR_COINS)));
  a_next_state_disp:   assert property (state==DISPENSING |-> next_state==IDLE);

  // Registered state evolution and datapath effects
  a_idle_coin_incr:    assert property (disable iff (reset || !past_valid)
                                        state==IDLE && coin_input |=> state==WAITING_FOR_COINS &&
                                                                   coins_inserted==$past(coins_inserted)+1);
  a_idle_hold:         assert property (disable iff (reset || !past_valid)
                                        state==IDLE && !coin_input |=> state==IDLE && $stable(coins_inserted));

  a_wait_coin_incr:    assert property (disable iff (reset || !past_valid)
                                        state==WAITING_FOR_COINS && coin_input |=> state==WAITING_FOR_COINS &&
                                                                           coins_inserted==$past(coins_inserted)+1);
  a_wait_dispense:     assert property (disable iff (reset || !past_valid)
                                        state==WAITING_FOR_COINS && !coin_input && button_input && coins_inserted>=price
                                        |=> state==DISPENSING && coins_inserted==$past(coins_inserted)-price);
  a_wait_hold_btn_ins: assert property (disable iff (reset || !past_valid)
                                        state==WAITING_FOR_COINS && !coin_input && button_input && coins_inserted<price
                                        |=> state==WAITING_FOR_COINS && $stable(coins_inserted));
  a_wait_hold_idle:    assert property (disable iff (reset || !past_valid)
                                        state==WAITING_FOR_COINS && !coin_input && !button_input
                                        |=> state==WAITING_FOR_COINS && $stable(coins_inserted));

  a_disp_to_idle:      assert property (state==DISPENSING |=> state==IDLE);
  a_coins_stable_disp: assert property (disable iff (reset || !past_valid) state==DISPENSING |=> $stable(coins_inserted));

  // Output behavior (these will flag bugs if violated)
  a_product_only_in_disp:     assert property (product_output |-> state==DISPENSING);
  a_product_low_outside_disp: assert property (state!=DISPENSING |-> product_output==0);
  a_product_asserted_in_disp: assert property (state==DISPENSING |=> product_output==1);
  a_display_stable:           assert property (disable iff (reset) $stable(display_output));

  // Legal cause for entering DISPENSING
  a_disp_entry_cause:  assert property (disable iff (reset || !past_valid)
                                        state==DISPENSING |-> $past(state)==WAITING_FOR_COINS &&
                                                                !$past(coin_input) &&
                                                                 $past(button_input) &&
                                                                 $past(coins_inserted)>=price);

  // Coins may only change per defined rules
  a_coins_change_only: assert property (disable iff (reset || !past_valid)
    (coins_inserted != $past(coins_inserted)) |->
      (( $past(state) inside {IDLE,WAITING_FOR_COINS} && $past(coin_input) &&
         coins_inserted==$past(coins_inserted)+1) ||
       ( $past(state)==WAITING_FOR_COINS && !$past(coin_input) && $past(button_input) &&
         $past(coins_inserted)>=price && coins_inserted==$past(coins_inserted)-price))
  );

  // Coverage
  c_exact_vend:        cover property (state==IDLE ##1 coin_input ##1 coin_input ##1 !coin_input && button_input ##1 state==DISPENSING);
  c_overpay_vend:      cover property (state==IDLE ##1 coin_input ##1 coin_input ##1 coin_input ##1 !coin_input && button_input
                                       ##1 state==DISPENSING ##1 coins_inserted==4'd1);
  c_insufficient_btn:  cover property (state==IDLE ##1 coin_input ##1 !coin_input && button_input ##1 state==WAITING_FOR_COINS);
  c_product_pulse:     cover property (state==DISPENSING ##1 product_output);

endmodule

bind vending_machine_fsm vending_machine_fsm_sva sva_checker();