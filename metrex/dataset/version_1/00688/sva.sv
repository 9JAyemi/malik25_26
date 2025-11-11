// SVA for vending_machine
// Bind into DUT to check behavior and cover key scenarios

module vending_machine_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  coin,
  input  logic [3:0]  selection,
  input  logic        dispense,
  input  logic [3:0]  change,
  input  logic [1:0]  state,
  input  logic [3:0]  coins_inserted,
  input  logic [3:0]  product_selected,
  input  logic [3:0]  change_due
);
  // State encodings (must match DUT)
  localparam IDLE     = 2'b00;
  localparam SELECT   = 2'b01;
  localparam DISPENSE = 2'b10;

  // ------------------------
  // Basic reset and legality
  // ------------------------
  // Reset drives all key regs/outs to 0 and IDLE
  property p_reset_values;
    @(posedge clk) reset |-> (state==IDLE && coins_inserted==0 && product_selected==0 && dispense==0 && change==0);
  endproperty
  assert property (p_reset_values);

  // State must remain legal
  property p_state_legal;
    @(posedge clk) disable iff (reset)
      1'b1 |-> (state inside {IDLE,SELECT,DISPENSE});
  endproperty
  assert property (p_state_legal);

  // ------------------------
  // IDLE behavior
  // ------------------------
  // On coin in IDLE, accumulate and go to SELECT; no overflow
  property p_idle_coin_add;
    @(posedge clk) disable iff (reset)
      (state==IDLE && coin!=0)
      |=> (state==SELECT
           && coins_inserted == $past(coins_inserted,1,reset) + $past(coin,1,reset));
  endproperty
  assert property (p_idle_coin_add);

  property p_idle_no_overflow;
    @(posedge clk) disable iff (reset)
      (state==IDLE && coin!=0)
      |-> ($past(coins_inserted,1,reset) + $past(coin,1,reset) <= 4'd15);
  endproperty
  assert property (p_idle_no_overflow);

  // If no coin in IDLE, stay put and keep values
  property p_idle_no_coin_stay;
    @(posedge clk) disable iff (reset)
      (state==IDLE && coin==0) |=> (state==IDLE && $stable(coins_inserted) && $stable(product_selected));
  endproperty
  assert property (p_idle_no_coin_stay);

  // ------------------------
  // SELECT behavior
  // ------------------------
  // Valid purchase A
  property p_select_to_dispense_A;
    @(posedge clk) disable iff (reset)
      (state==SELECT && selection==4'b0001 && coins_inserted>=4)
      |=> (state==DISPENSE
           && product_selected == $past(selection,1,reset)
           && coins_inserted == $past(coins_inserted,1,reset) - 4);
  endproperty
  assert property (p_select_to_dispense_A);

  // Valid purchase B
  property p_select_to_dispense_B;
    @(posedge clk) disable iff (reset)
      (state==SELECT && selection==4'b0010 && coins_inserted>=6)
      |=> (state==DISPENSE
           && product_selected == $past(selection,1,reset)
           && coins_inserted == $past(coins_inserted,1,reset) - 6);
  endproperty
  assert property (p_select_to_dispense_B);

  // Insufficient funds: remain in SELECT and do not change money/selection
  property p_select_insufficient_stay;
    @(posedge clk) disable iff (reset)
      (state==SELECT &&
        ((selection==4'b0001 && coins_inserted<4) || (selection==4'b0010 && coins_inserted<6)))
      |=> (state==SELECT && $stable(coins_inserted) && $stable(product_selected));
  endproperty
  assert property (p_select_insufficient_stay);

  // Invalid selection (non 0/1/2): stay in SELECT and do not change money/selection
  property p_select_invalid_stay;
    @(posedge clk) disable iff (reset)
      (state==SELECT && !(selection inside {4'b0000,4'b0001,4'b0010}))
      |=> (state==SELECT && $stable(coins_inserted) && $stable(product_selected));
  endproperty
  assert property (p_select_invalid_stay);

  // selection==0: no action, remain in SELECT and hold values
  property p_select_zero_noop;
    @(posedge clk) disable iff (reset)
      (state==SELECT && selection==4'b0000)
      |=> (state==SELECT && $stable(coins_inserted) && $stable(product_selected));
  endproperty
  assert property (p_select_zero_noop);

  // ------------------------
  // DISPENSE behavior
  // ------------------------
  // DISPENSE cycle must assert dispense and next cycle go to IDLE
  property p_dispense_to_idle_and_pulse;
    @(posedge clk) disable iff (reset)
      (state==DISPENSE) |=> (state==IDLE && dispense==1'b1);
  endproperty
  assert property (p_dispense_to_idle_and_pulse);

  // Dispense should be a single-cycle pulse
  property p_dispense_one_cycle;
    @(posedge clk) disable iff (reset)
      dispense |=> !dispense;
  endproperty
  assert property (p_dispense_one_cycle);

  // Change value should equal leftover money from purchase (observed two cycles after decision)
  property p_change_value_A;
    @(posedge clk) disable iff (reset)
      (state==SELECT && selection==4'b0001 && coins_inserted>=4)
      |-> ##2 (change == $past(coins_inserted,2,reset) - 4);
  endproperty
  assert property (p_change_value_A);

  property p_change_value_B;
    @(posedge clk) disable iff (reset)
      (state==SELECT && selection==4'b0010 && coins_inserted>=6)
      |-> ##2 (change == $past(coins_inserted,2,reset) - 6);
  endproperty
  assert property (p_change_value_B);

  // Change should not spontaneously change outside DISPENSE
  property p_change_stable_outside_dispense;
    @(posedge clk) disable iff (reset)
      (state!=DISPENSE) |=> $stable(change);
  endproperty
  assert property (p_change_stable_outside_dispense);

  // ------------------------
  // Coverage
  // ------------------------
  // Purchase A path
  cover property (@(posedge clk) disable iff (reset)
    state==SELECT && selection==4'b0001 && coins_inserted>=4
    ##1 state==DISPENSE ##1 state==IDLE);

  // Purchase B path
  cover property (@(posedge clk) disable iff (reset)
    state==SELECT && selection==4'b0010 && coins_inserted>=6
    ##1 state==DISPENSE ##1 state==IDLE);

  // Exact change A and B
  cover property (@(posedge clk) disable iff (reset)
    state==SELECT && selection==4'b0001 && coins_inserted==4 ##2 change==0);
  cover property (@(posedge clk) disable iff (reset)
    state==SELECT && selection==4'b0010 && coins_inserted==6 ##2 change==0);

  // Insufficient funds held in SELECT
  cover property (@(posedge clk) disable iff (reset)
    state==SELECT && selection==4'b0001 && coins_inserted<4 ##1 state==SELECT);

  // Invalid selection held in SELECT
  cover property (@(posedge clk) disable iff (reset)
    state==SELECT && !(selection inside {4'b0000,4'b0001,4'b0010}) ##1 state==SELECT);

endmodule

// Bind into the DUT
bind vending_machine vending_machine_sva vmsva (
  .clk(clk),
  .reset(reset),
  .coin(coin),
  .selection(selection),
  .dispense(dispense),
  .change(change),
  .state(state),
  .coins_inserted(coins_inserted),
  .product_selected(product_selected),
  .change_due(change_due)
);