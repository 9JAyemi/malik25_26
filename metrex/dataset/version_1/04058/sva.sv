// Bindable SVA for delay_30_degrees
module delay_30_degrees_sva;

  default clocking cb @(posedge clk_i); endclocking

  // State legality and basic reset behavior
  assert property (state inside {RESET,INIT,CHANGE_POSITION,DELAY_30_DEGREES,APPLY_CHANGE,IDLE});
  assert property ($onehot(state));
  assert property (rst_i |=> state==RESET);
  assert property (state==RESET |-> speed_count==0 && speed_divider==0 && position_o==3'b001);
  assert property (disable iff (rst_i) state==$past(next_state));
  assert property (disable iff (rst_i) state==RESET |=> state==INIT);

  // FSM transitions
  assert property (disable iff (rst_i) state==INIT && (position_i!=position_old) |=> state==CHANGE_POSITION);
  assert property (disable iff (rst_i) state==INIT && (position_i==position_old) |=> state==INIT);
  assert property (disable iff (rst_i) state==CHANGE_POSITION |=> state==DELAY_30_DEGREES);
  assert property (disable iff (rst_i) state==DELAY_30_DEGREES && (delay_count > speed_divider) |=> state==APPLY_CHANGE);
  assert property (disable iff (rst_i) state==DELAY_30_DEGREES && !(delay_count > speed_divider) |=> state==DELAY_30_DEGREES);
  assert property (disable iff (rst_i) state==APPLY_CHANGE |=> state==IDLE);
  assert property (disable iff (rst_i) state==IDLE && (position_i!=position_old) |=> state==CHANGE_POSITION);
  assert property (disable iff (rst_i) state==IDLE && (position_i==position_old) |=> state==IDLE);

  // Counters and divider behavior
  assert property (disable iff (rst_i) speed_count <= MAX_SPEED_COUNT);
  assert property (disable iff (rst_i)
    $past(state)==CHANGE_POSITION |-> speed_divider == ($past(speed_count) >> 1) && speed_count==0 && delay_count==0);
  assert property (disable iff (rst_i)
    $past(state) inside {INIT,DELAY_30_DEGREES,APPLY_CHANGE,IDLE} && $past(speed_count) < MAX_SPEED_COUNT
    |-> speed_count == $past(speed_count)+1);
  assert property (disable iff (rst_i)
    $past(state) inside {INIT,DELAY_30_DEGREES,APPLY_CHANGE,IDLE} && $past(speed_count) >= MAX_SPEED_COUNT
    |-> speed_count == $past(speed_count));
  assert property (disable iff (rst_i) $past(state)==DELAY_30_DEGREES |-> delay_count == $past(delay_count)+1);
  // stability constraints
  assert property (disable iff (rst_i) !($past(state) inside {CHANGE_POSITION,RESET}) |-> speed_divider == $past(speed_divider));
  assert property (disable iff (rst_i) !($past(state) inside {DELAY_30_DEGREES,CHANGE_POSITION}) |-> delay_count == $past(delay_count));

  // Output mapping and stability
  assert property (disable iff (rst_i) position_o inside {3'b001,3'b010,3'b011,3'b100,3'b101,3'b110});
  assert property (disable iff (rst_i) $past(state)==APPLY_CHANGE && $past(position_i)==3'b101 |-> position_o==3'b100);
  assert property (disable iff (rst_i) $past(state)==APPLY_CHANGE && $past(position_i)==3'b100 |-> position_o==3'b110);
  assert property (disable iff (rst_i) $past(state)==APPLY_CHANGE && $past(position_i)==3'b110 |-> position_o==3'b010);
  assert property (disable iff (rst_i) $past(state)==APPLY_CHANGE && $past(position_i)==3'b010 |-> position_o==3'b011);
  assert property (disable iff (rst_i) $past(state)==APPLY_CHANGE && $past(position_i)==3'b011 |-> position_o==3'b001);
  assert property (disable iff (rst_i) $past(state)==APPLY_CHANGE && $past(position_i)==3'b001 |-> position_o==3'b101);
  assert property (disable iff (rst_i) !($past(state) inside {APPLY_CHANGE,RESET}) |-> position_o == $past(position_o));

  // position_old update/hold
  assert property (disable iff (rst_i) $past(state)==APPLY_CHANGE |-> position_old == $past(position_i));
  assert property (disable iff (rst_i) $past(state)!=APPLY_CHANGE |-> position_old == $past(position_old));

  // Input legality (6-step commutation codes only)
  assert property (disable iff (rst_i) position_i inside {3'b001,3'b010,3'b011,3'b100,3'b101,3'b110});

  // Coverage
  cover property (disable iff (rst_i) state==RESET ##1 state==INIT);
  cover property (disable iff (rst_i)
    state==INIT && position_i!=position_old ##1 state==CHANGE_POSITION
    ##1 (state==DELAY_30_DEGREES)[*1:$] ##1 state==APPLY_CHANGE ##1 state==IDLE);
  cover property (disable iff (rst_i) speed_count==MAX_SPEED_COUNT);
  cover property (disable iff (rst_i) $past(state)==APPLY_CHANGE && $past(position_i)==3'b101 && position_o==3'b100);
  cover property (disable iff (rst_i) $past(state)==APPLY_CHANGE && $past(position_i)==3'b100 && position_o==3'b110);
  cover property (disable iff (rst_i) $past(state)==APPLY_CHANGE && $past(position_i)==3'b110 && position_o==3'b010);
  cover property (disable iff (rst_i) $past(state)==APPLY_CHANGE && $past(position_i)==3'b010 && position_o==3'b011);
  cover property (disable iff (rst_i) $past(state)==APPLY_CHANGE && $past(position_i)==3'b011 && position_o==3'b001);
  cover property (disable iff (rst_i) $past(state)==APPLY_CHANGE && $past(position_i)==3'b001 && position_o==3'b101);

endmodule

bind delay_30_degrees delay_30_degrees_sva sva_inst();