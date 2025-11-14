// SVA for Booth_Multiplier
// Bindable checker focusing on FSM, busy/start protocol, product updates, and basic coverage.

module Booth_Multiplier_sva (
  input logic                  clock,
  input logic signed [3:0]     multiplicand,
  input logic signed [3:0]     multiplier,
  input logic                  start,
  input logic signed [7:0]     product,
  input logic                  busy,
  // internal DUT regs
  input logic signed [7:0]     product_reg,
  input logic        [2:0]     state,
  input logic                  busy_reg
);

  default clocking cb @(posedge clock); endclocking

  // Past-valid to guard $past usages
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clock) past_valid <= 1'b1;

  // Basic sanity/knownness
  a_known_inputs:    assert property (@cb !$isunknown({start, multiplicand, multiplier}));
  a_known_outputs:   assert property (@cb past_valid |-> !$isunknown({product, busy}));
  a_state_legal:     assert property (@cb (state inside {3'b000,3'b001,3'b010,3'b011,3'b100}));

  // Output mapping to internal regs
  a_prod_maps:       assert property (@cb product == product_reg);
  a_busy_maps:       assert property (@cb busy   == busy_reg);

  // Start protocol
  a_start_when_idle: assert property (@cb start |-> (state == 3'b001 && !busy));
  a_busy_rise_src:   assert property (@cb $rose(busy) |-> $past(state==3'b001 && start));

  // Busy deassert only from 100 with multiplier==0
  a_busy_fall_cause: assert property (@cb $fell(busy) |-> $past(state==3'b100 && multiplier==4'b0000));

  // FSM transitions
  a_000_to_001:      assert property (@cb state==3'b000 |=> (state==3'b001 && product==8'sd0));
  a_001_hold:        assert property (@cb state==3'b001 && !start |=> (state==3'b001 && $stable(busy) && $stable(product)));
  a_001_start:       assert property (@cb state==3'b001 && start |=> (state==3'b010 && busy));
  a_010_to_011:      assert property (@cb state==3'b010 |=> state==3'b011);
  a_011_to_100:      assert property (@cb state==3'b011 |=> state==3'b100);
  a_100_branch0:     assert property (@cb state==3'b100 && multiplier==4'b0000 |=> (state==3'b001 && !busy));
  a_100_branch1:     assert property (@cb state==3'b100 && multiplier!=4'b0000 |=> (state==3'b010));

  // Busy must hold during active processing states (except deassertion next cycle from 100/zero)
  a_busy_in_active:  assert property (@cb (state inside {3'b010,3'b011}) |-> busy);

  // Product update rules
  a_prod_sub:        assert property (@cb disable iff(!past_valid)
                                      state==3'b010 && (multiplier[0]==1'b1)
                                      |=> product == $past(product) - $signed(multiplicand));
  a_prod_add:        assert property (@cb disable iff(!past_valid)
                                      state==3'b010 && (multiplier[0]==1'b0)
                                      |=> product == $past(product) + $signed(multiplicand));
  a_prod_stable_else:assert property (@cb (state inside {3'b001,3'b011,3'b100}) |-> $stable(product));

  // Minimal functional/flow coverage
  c_handshake:  cover property (@cb state==3'b001 && start ##1 (busy && state==3'b010));
  c_add_path:   cover property (@cb state==3'b010 && multiplier[0]==1'b0);
  c_sub_path:   cover property (@cb state==3'b010 && multiplier[0]==1'b1);
  c_loop:       cover property (@cb state==3'b010 ##1 state==3'b011 ##1 state==3'b100 ##1 state==3'b010);
  c_complete:   cover property (@cb state==3'b001 && start ##1 state==3'b010 [*1:$] ##1 (state==3'b100 && multiplier==4'b0000) ##1 (!busy && state==3'b001));

endmodule

bind Booth_Multiplier Booth_Multiplier_sva sva (
  .clock(clock),
  .multiplicand(multiplicand),
  .multiplier(multiplier),
  .start(start),
  .product(product),
  .busy(busy),
  .product_reg(product_reg),
  .state(state),
  .busy_reg(busy_reg)
);