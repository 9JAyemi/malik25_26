// SVA checker for traffic_light_controller
module traffic_light_controller_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        green,
  input  logic        yellow,
  input  logic        red,
  input  logic [1:0]  state_reg,
  input  logic [3:0]  green_counter,
  input  logic [3:0]  yellow_counter,
  input  logic [3:0]  red_counter
);
  // Mirror encodings
  localparam [1:0] GREEN  = 2'b00;
  localparam [1:0] YELLOW = 2'b01;
  localparam [1:0] RED    = 2'b10;

  // Reset behavior (synchronous)
  a_reset_values:
    assert property (@(posedge clk)
      reset |-> (state_reg==GREEN && green_counter==0 && yellow_counter==0 && red_counter==0
                 && green==1'b1 && yellow==1'b0 && red==1'b0));

  // No X/Z on key signals
  a_no_x:
    assert property (@(posedge clk)
      !$isunknown({state_reg,green_counter,yellow_counter,red_counter,green,yellow,red}));

  // Legal state encoding only
  a_state_legal:
    assert property (@(posedge clk) disable iff (reset)
      state_reg inside {GREEN,YELLOW,RED});

  // One-hot outputs and mapping to state
  a_onehot:
    assert property (@(posedge clk)
      $onehot({green,yellow,red}));
  a_map_green:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==GREEN)  |-> (green && !yellow && !red));
  a_map_yellow:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==YELLOW) |-> (!green && yellow && !red));
  a_map_red:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==RED)    |-> (!green && !yellow && red));

  // Outputs stable when state holds
  a_outputs_stable_when_state_holds:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==$past(state_reg)) |-> $stable({green,yellow,red}));

  // Allowed transition order only
  a_transitions_ordered:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg != $past(state_reg)) |->
        (($past(state_reg)==GREEN  && state_reg==YELLOW) ||
         ($past(state_reg)==YELLOW && state_reg==RED)    ||
         ($past(state_reg)==RED    && state_reg==GREEN)));

  // Counters reset on state entry
  a_gc_zero_on_entry:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==GREEN  && $past(state_reg)!=GREEN)  |-> (green_counter==0));
  a_yc_zero_on_entry:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==YELLOW && $past(state_reg)!=YELLOW) |-> (yellow_counter==0));
  a_rc_zero_on_entry:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==RED    && $past(state_reg)!=RED)    |-> (red_counter==0));

  // Only active state's counter increments; others hold (when staying in same state)
  a_gc_inc_and_others_hold:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==GREEN && $past(state_reg)==GREEN) |->
        ((green_counter == $past(green_counter)+1) &&
         $stable({yellow_counter,red_counter})));
  a_yc_inc_and_others_hold:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==YELLOW && $past(state_reg)==YELLOW) |->
        ((yellow_counter == $past(yellow_counter)+1) &&
         $stable({green_counter,red_counter})));
  a_rc_inc_and_others_hold:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==RED && $past(state_reg)==RED) |->
        ((red_counter == $past(red_counter)+1) &&
         $stable({green_counter,yellow_counter})));

  // Counter bounds within state
  a_gc_bounds:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==GREEN)  |-> (green_counter  inside {[0:9]}));
  a_yc_bounds:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==YELLOW) |-> (yellow_counter inside {[0:1]}));
  a_rc_bounds:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==RED)    |-> (red_counter    inside {[0:7]}));

  // Transitions happen on terminal counts with proper resets
  a_green_to_yellow_on_9:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==GREEN && green_counter==9) |=> (state_reg==YELLOW && green_counter==0));
  a_yellow_to_red_on_1:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==YELLOW && yellow_counter==1) |=> (state_reg==RED && yellow_counter==0));
  a_red_to_green_on_7:
    assert property (@(posedge clk) disable iff (reset)
      (state_reg==RED && red_counter==7) |=> (state_reg==GREEN && red_counter==0));

  // Dwell length coverage of a full cycle: G(10) -> Y(2) -> R(8) -> G
  c_full_cycle:
    cover property (@(posedge clk) disable iff (reset)
      (state_reg==GREEN)[*10] ##1 (state_reg==YELLOW)[*2] ##1 (state_reg==RED)[*8] ##1 (state_reg==GREEN));

  // Cover each transition
  c_g2y: cover property (@(posedge clk) disable iff (reset)
    (state_reg==GREEN && green_counter==9) ##1 (state_reg==YELLOW));
  c_y2r: cover property (@(posedge clk) disable iff (reset)
    (state_reg==YELLOW && yellow_counter==1) ##1 (state_reg==RED));
  c_r2g: cover property (@(posedge clk) disable iff (reset)
    (state_reg==RED && red_counter==7) ##1 (state_reg==GREEN));

endmodule

// Bind into DUT (accesses internal regs via named association)
bind traffic_light_controller traffic_light_controller_sva sva (
  .clk(clk),
  .reset(reset),
  .green(green),
  .yellow(yellow),
  .red(red),
  .state_reg(state_reg),
  .green_counter(green_counter),
  .yellow_counter(yellow_counter),
  .red_counter(red_counter)
);