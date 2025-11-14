// SVA for counter_4bit
// Bind this module to the DUT to check behavior and collect coverage.

module counter_4bit_sva (
  input clk,
  input reset,
  input load,
  input up_down,
  input [3:0] D,
  input [3:0] Q
);

  // Control inputs must be known; D must be known when used
  a_ctrl_known: assert property (@(posedge clk) !$isunknown({reset,load,up_down}));
  a_D_known_when_load: assert property (@(posedge clk) load |-> !$isunknown(D));

  // Reset: on any cycle where reset was high, Q must be 0 in the next cycle
  a_reset_next_zero: assert property (@(posedge clk) $past(reset) |-> (Q == 4'd0));

  // Load has priority over up/down; next Q equals sampled D when load (and not in reset)
  a_load_next_QeqD: assert property (@(posedge clk) $past(load && !reset) |-> (Q == $past(D)));

  // Count up when enabled (no reset, no load)
  a_count_up: assert property (@(posedge clk)
    $past(!reset && !load && up_down) |-> (Q == ($past(Q)+5'd1)[3:0]));

  // Count down when enabled (no reset, no load)
  a_count_down: assert property (@(posedge clk)
    $past(!reset && !load && !up_down) |-> (Q == ($past(Q)-5'd1)[3:0]));

  // Coverage: wrap-around up and down
  c_wrap_up:   cover property (@(posedge clk)
    $past(!reset && !load && up_down && ($past(Q)==4'hF)) |-> (Q==4'h0));
  c_wrap_down: cover property (@(posedge clk)
    $past(!reset && !load && !up_down && ($past(Q)==4'h0)) |-> (Q==4'hF));

  // Coverage: load overrides up/down, including when up_down=1
  c_load_overrides: cover property (@(posedge clk)
    $past(load && !reset && up_down) |-> (Q == $past(D)));

  // Coverage: direction change (up then down in consecutive cycles)
  c_up_then_down: cover property (@(posedge clk)
    (!reset && !load && up_down) ##1 (!reset && !load && !up_down));

  // Coverage: load a couple of representative values
  c_load_0: cover property (@(posedge clk) $past(load && !reset && D==4'h0) |-> (Q==4'h0));
  c_load_F: cover property (@(posedge clk) $past(load && !reset && D==4'hF) |-> (Q==4'hF));

endmodule

bind counter_4bit counter_4bit_sva sva_i (.clk(clk), .reset(reset), .load(load), .up_down(up_down), .D(D), .Q(Q));