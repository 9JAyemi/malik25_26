// SVA checker bound into the DUT’s scope. Concurrent, event-driven on any comb change.
module vending_machine_controller_sva;

  // Combinational sampling event
  event comb_ev;
  always @(product_sel or money_in or dispense or change or total_cost or remaining_cost or change_due) -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  // No X/Z on key signals
  a_no_x: assert property (!$isunknown({product_sel, money_in, dispense, change, total_cost, remaining_cost, change_due})));

  // total_cost mapping correctness
  a_cost_map_00: assert property ((product_sel==2'b00) |-> (total_cost==PRICE_1));
  a_cost_map_01: assert property ((product_sel==2'b01) |-> (total_cost==PRICE_2));
  a_cost_map_10: assert property ((product_sel==2'b10) |-> (total_cost==PRICE_3));
  a_cost_map_11: assert property ((product_sel==2'b11) |-> (total_cost==PRICE_4));
  a_cost_set:    assert property (total_cost inside {PRICE_1,PRICE_2,PRICE_3,PRICE_4});

  // remaining_cost computation
  a_rem_under: assert property ((money_in <  total_cost) |-> (remaining_cost == (total_cost - money_in)));
  a_rem_ge:    assert property ((money_in >= total_cost) |-> (remaining_cost == 7'd0));

  // dispense equivalence
  a_disp_equiv: assert property (dispense == (money_in >= total_cost));

  // change_due and change behavior
  a_change_due_calc:      assert property (change_due == (money_in - total_cost)[5:0]);
  a_change_when_disp:     assert property (dispense |-> (change == change_due));
  a_change_when_no_disp:  assert property (!dispense |-> (change == 6'd0));

  // Optional: flag potential truncation if environment overpays too much
  a_change_no_overflow: assert property (dispense |-> ((money_in - total_cost) <= 8'd63)));

  // Functional coverage
  c_sel00_disp:   cover property ((product_sel==2'b00) && dispense);
  c_sel01_disp:   cover property ((product_sel==2'b01) && dispense);
  c_sel10_disp:   cover property ((product_sel==2'b10) && dispense);
  c_sel11_disp:   cover property ((product_sel==2'b11) && dispense);
  c_exact_pay:    cover property (dispense && (money_in == total_cost) && (change==6'd0));
  c_underpay:     cover property (!dispense && (money_in < total_cost) && (remaining_cost > 0));
  c_overpay_wchg: cover property (dispense && (money_in > total_cost) && ((money_in - total_cost) inside {[8'd1:8'd63]}));
  c_change_max63: cover property (dispense && ((money_in - total_cost) == 8'd63));
  c_overflow_try: cover property (dispense && ((money_in - total_cost) >= 8'd64));

endmodule

// Bind into all instances of the DUT
bind vending_machine_controller vending_machine_controller_sva sva_vending_machine_controller();