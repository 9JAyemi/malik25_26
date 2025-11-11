// SVA for top_module
// Focus: correctness, gating, wrap logic, ranges, X-usage, and key coverage

module top_module_sva (
  input  logic        clk,
  input  logic        areset,
  input  logic        load,
  input  logic        up_down,
  input  logic        select,
  input  logic [4:0]  counter4,
  input  logic [2:0]  counter3,
  input  logic [5:0]  sum,
  // internal DUT regs (bound hierarchically)
  input  logic [4:0]  counter4_next,
  input  logic [2:0]  counter3_next
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!areset);

  // Reset holds counters at 0
  a_hold_in_reset: assert property (!areset |-> (counter4==5'd0 && counter3==3'd0));

  // Sum must always reflect counters
  a_sum_correct:   assert property (sum == counter4 + counter3);

  // Counters update only on load, and only the selected one
  a_no_update_when_no_load: assert property (!load |=> counter4==$past(counter4) && counter3==$past(counter3));
  a_load_sel4_updates:      assert property ( load &&  select |=> counter4==$past(counter4_next) && counter3==$past(counter3));
  a_load_sel3_updates:      assert property ( load && !select |=> counter3==$past(counter3_next) && counter4==$past(counter4));

  // Next regs are held when not written
  a_next_hold_when_load:    assert property (load |=> counter4_next==$past(counter4_next) && counter3_next==$past(counter3_next));

  // Next-state generation (compute on !load side), with wrap
  a_next4_inc: assert property (!load &&  select &&  up_down |=> counter4_next == (($past(counter4)==5'd15) ? 5'd0 : $past(counter4)+1));
  a_next4_dec: assert property (!load &&  select && !up_down |=> counter4_next == (($past(counter4)==5'd0)  ? 5'd15: $past(counter4)-1));
  a_next3_inc: assert property (!load && !select &&  up_down |=> counter3_next == (($past(counter3)==3'd7)  ? 3'd0 : $past(counter3)+1));
  a_next3_dec: assert property (!load && !select && !up_down |=> counter3_next == (($past(counter3)==3'd0)  ? 3'd7 : $past(counter3)-1));

  // Only the selected next reg updates on compute cycles
  a_next3_stable_when_sel4: assert property (!load &&  select |=> counter3_next==$past(counter3_next));
  a_next4_stable_when_sel3: assert property (!load && !select |=> counter4_next==$past(counter4_next));

  // Valid ranges; also catch use of uninitialized next on load
  a_counter_ranges: assert property (counter4<=5'd15 && counter3<=3'd7);
  a_no_x_use4:      assert property (load &&  select |-> !$isunknown($past(counter4_next)));
  a_no_x_use3:      assert property (load && !select |-> !$isunknown($past(counter3_next)));

  // Optional sanity: sum stable if counters stable across a clock
  a_sum_stable_if_counters_stable: assert property ((counter4==$past(counter4) && counter3==$past(counter3)) |-> sum==$past(sum));

  // Coverage: exercise both directions, wraps, and both selects
  c_sel4_inc_wrap: cover property (!load &&  select &&  up_down && counter4==5'd15 ##1 load &&  select ##1 counter4==5'd0);
  c_sel4_dec_wrap: cover property (!load &&  select && !up_down && counter4==5'd0  ##1 load &&  select ##1 counter4==5'd15);
  c_sel3_inc_wrap: cover property (!load && !select &&  up_down && counter3==3'd7  ##1 load && !select ##1 counter3==3'd0);
  c_sel3_dec_wrap: cover property (!load && !select && !up_down && counter3==3'd0  ##1 load && !select ##1 counter3==3'd7);
  c_both_selects:  cover property (load &&  select) and cover property (load && !select);
  c_sum_extremes0: cover property (counter4==5'd0  && counter3==3'd0  && sum==6'd0);
  c_sum_extremes1: cover property (counter4==5'd15 && counter3==3'd7  && sum==6'd22);

endmodule

// Bind into DUT (allows access to internal counter*_next regs)
bind top_module top_module_sva u_top_module_sva (
  .clk(clk),
  .areset(areset),
  .load(load),
  .up_down(up_down),
  .select(select),
  .counter4(counter4),
  .counter3(counter3),
  .sum(sum),
  .counter4_next(counter4_next),
  .counter3_next(counter3_next)
);