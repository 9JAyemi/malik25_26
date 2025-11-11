// SVA for vending_machine
// Bind this module to the DUT: bind vending_machine vending_machine_sva svacheck();

module vending_machine_sva;

  // Use DUT scope signals directly via bind
  // DUT ports/regs: clk,rst,start,cancel,coin,display,dispense,amount_inserted,item_selected
  default clocking cb @(posedge clk); endclocking
  // For most checks ignore cycles with rst=1
  `define DISABLE disable iff (rst)

  // Basic invariants and ranges
  a_ranges: assert property (@cb (amount_inserted <= 7'd99) && (display <= 7'd99)
                                  && (dispense <= 2'd3) && (item_selected <= 2'd3))
    else $error("Range violation");

  a_no_x: assert property (@cb !$isunknown({amount_inserted, item_selected, display, dispense}))
    else $error("X/Z detected on state/outputs");

  // Reset behavior
  a_reset_clear: assert property (@cb rst |=> amount_inserted==0 && item_selected==0 && display==0 && dispense==0)
    else $error("Reset did not clear state/outputs");

  // START branch behavior
  a_start_incr: assert property (@cb `DISABLE start && (amount_inserted + coin <= 7'd99)
                                 |=> amount_inserted == $past(amount_inserted)+$past(coin)
                                  && display == $past(amount_inserted))
    else $error("Start increment/update mismatch");

  a_start_saturate: assert property (@cb `DISABLE start && (amount_inserted + coin > 7'd99)
                                      |=> amount_inserted == $past(amount_inserted)
                                       && display == 7'd99)
    else $error("Start saturate mismatch");

  // CANCEL branch behavior
  a_cancel_clear: assert property (@cb `DISABLE !start && cancel |=> amount_inserted==0 && display==0)
    else $error("Cancel did not clear amount/display");

  // VEND branch actually taken by this RTL (item 1 has priority for any amount>=25)
  a_vend1_taken: assert property (@cb `DISABLE !start && !cancel && item_selected==0 && (amount_inserted >= 7'd25)
                                  |=> item_selected==2'd1
                                   && amount_inserted == $past(amount_inserted) - 7'd25
                                   && display==0
                                   && dispense == $past(item_selected))
    else $error("Vend1 transaction mismatch");

  // ELSE branch behavior when no other branch applies
  a_else_hold: assert property (@cb `DISABLE !start && !cancel && (item_selected!=0 || amount_inserted < 7'd25)
                                |=> display == $past(amount_inserted)
                                 && dispense == 2'd0
                                 && amount_inserted == $past(amount_inserted)
                                 && item_selected == $past(item_selected))
    else $error("Idle/else branch mismatch");

  // State-change causality
  a_amt_change_cause: assert property (@cb `DISABLE (amount_inserted != $past(amount_inserted))
                                        |-> ($past(start) && ($past(amount_inserted)+$past(coin) <= 7'd99))
                                         || ($past(!start && !cancel && item_selected==0 && amount_inserted>=7'd25)))
    else $error("Unexpected amount_inserted change");

  a_itemsel_change_cause: assert property (@cb `DISABLE (item_selected != $past(item_selected))
                                             |-> ($past(!start && !cancel && item_selected==0 && amount_inserted>=7'd25)
                                                  && item_selected==2'd1))
    else $error("Unexpected item_selected change");

  // Dispense at vend time equals previous item_selected (per RTL)
  a_dispense_prev_itemsel: assert property (@cb `DISABLE (item_selected==2'd1 && $past(item_selected)==2'd0)
                                            |-> dispense == 2'd0)
    else $error("Dispense not equal to previous item_selected during vend");

  // Safety: display never exceeds 99
  a_display_cap: assert property (@cb display <= 7'd99)
    else $error("Display exceeded 99");

  // Coverage: exercise primary behaviors and expose unreachable branches

  // Reset then idle
  c_reset: cover property (@cb rst ##1 !rst && amount_inserted==0 && item_selected==0 && display==0 && dispense==0);

  // Start increments within cap
  c_start_incr: cover property (@cb `DISABLE start && (amount_inserted + coin <= 7'd99));

  // Start saturates to 99
  c_start_sat: cover property (@cb `DISABLE start && (amount_inserted + coin > 7'd99) ##1 display==7'd99);

  // Cancel after some accumulation
  c_cancel: cover property (@cb `DISABLE (start && (amount_inserted + coin <= 7'd99))[->2] ##1 (!start && cancel) ##1 (amount_inserted==0 && display==0));

  // Vend item 1 on exact price
  c_vend1_exact: cover property (@cb `DISABLE !start && !cancel && item_selected==0 && amount_inserted==7'd25 ##1 item_selected==2'd1);

  // Vend item 1 on greater-than price
  c_vend1_gt: cover property (@cb `DISABLE !start && !cancel && item_selected==0 && amount_inserted>7'd25 ##1 item_selected==2'd1);

  // Attempt to cover item 2 vend (expected unreachable with current priority)
  c_vend2: cover property (@cb `DISABLE !start && !cancel && item_selected==0 && amount_inserted>=7'd50 ##1 item_selected==2'd2);

  // Attempt to cover item 3 vend (expected unreachable with current priority)
  c_vend3: cover property (@cb `DISABLE !start && !cancel && item_selected==0 && amount_inserted>=7'd75 ##1 item_selected==2'd3);

  // Cover display tracking in idle
  c_idle_display: cover property (@cb `DISABLE !start && !cancel && (item_selected!=0 || amount_inserted<7'd25) ##1 display==$past(amount_inserted));

  // Cover all coin encodings seen under start
  c_coin0: cover property (@cb `DISABLE start && coin==2'b00);
  c_coin1: cover property (@cb `DISABLE start && coin==2'b01);
  c_coin2: cover property (@cb `DISABLE start && coin==2'b10);
  c_coin3: cover property (@cb `DISABLE start && coin==2'b11);

endmodule