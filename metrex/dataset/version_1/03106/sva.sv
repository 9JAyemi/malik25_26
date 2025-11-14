// SVA for mealy_state_machine
module mealy_state_machine_sva
  #(parameter logic [2:0] S0 = 3'b001,
                        S1 = 3'b010,
                        S2 = 3'b100)
(
  input logic        clk,
  input logic        reset,
  input logic        a,
  input logic        b,
  input logic        x,
  input logic        y,
  input logic [2:0]  state,
  input logic [2:0]  next_state
);

  // State encoding/health
  assert property (@(posedge clk) state inside {S0,S1,S2});
  assert property (@(posedge clk) !$isunknown(state));
  assert property (@(posedge clk) $onehot(state));

  // Reset holds state in S0 while asserted
  assert property (@(posedge clk) reset |-> state==S0);

  // Combinational next_state function
  assert property (@(posedge clk) disable iff (reset) (state==S0) |-> next_state == (a ? S1 : S0));
  assert property (@(posedge clk) disable iff (reset) (state==S1) |-> next_state == ((b==1'b0) ? S2 : S0));
  assert property (@(posedge clk) disable iff (reset) (state==S2) |-> next_state == (a ? S1 : S2));
  assert property (@(posedge clk) ((state inside {S0,S1,S2}) && !$isunknown({a,b})) |-> !$isunknown(next_state));

  // Registered state update equals prior-cycle next_state (skip first cycle after reset)
  assert property (@(posedge clk) (!reset && !$past(reset)) |-> state == $past(next_state));

  // Sequential transition behavior
  assert property (@(posedge clk) (!$past(reset) && $past(state)==S0) |-> state == ($past(a) ? S1 : S0));
  assert property (@(posedge clk) (!$past(reset) && $past(state)==S1) |-> state == (($past(b)==1'b0) ? S2 : S0));
  assert property (@(posedge clk) (!$past(reset) && $past(state)==S2) |-> state == ($past(a) ? S1 : S2));

  // Output decoding and health
  assert property (@(posedge clk) (state==S0) |-> (x==1'b0 && y==1'b0));
  assert property (@(posedge clk) (state==S1) |-> (x==1'b1 && y==1'b0));
  assert property (@(posedge clk) (state==S2) |-> (x==1'b0 && y==1'b1));
  assert property (@(posedge clk) !(x && y));
  assert property (@(posedge clk) !$isunknown({x,y}));

  // Coverage: states, outputs, and all transitions (including self-loops)
  cover property (@(posedge clk) disable iff (reset) state==S0);
  cover property (@(posedge clk) disable iff (reset) state==S1);
  cover property (@(posedge clk) disable iff (reset) state==S2);
  cover property (@(posedge clk) disable iff (reset) state==S0 &&  a ##1 state==S1);
  cover property (@(posedge clk) disable iff (reset) state==S0 && !a ##1 state==S0);
  cover property (@(posedge clk) disable iff (reset) state==S1 && !b ##1 state==S2);
  cover property (@(posedge clk) disable iff (reset) state==S1 &&  b ##1 state==S0);
  cover property (@(posedge clk) disable iff (reset) state==S2 &&  a ##1 state==S1);
  cover property (@(posedge clk) disable iff (reset) state==S2 && !a ##1 state==S2);
  cover property (@(posedge clk) disable iff (reset) x==1 && y==0);
  cover property (@(posedge clk) disable iff (reset) x==0 && y==1);
  cover property (@(posedge clk) reset ##1 !reset && state==S0);

endmodule

// Bind into DUT
bind mealy_state_machine
  mealy_state_machine_sva #(.S0(S0), .S1(S1), .S2(S2))
  mealy_state_machine_sva_i (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .x(x),
    .y(y),
    .state(state),
    .next_state(next_state)
  );