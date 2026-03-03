// SVA for up_down_counter
module up_down_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        up,
  input logic        down,
  input logic [2:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (cb !$isunknown({reset,up,down,count}));

  // Asynchronous reset: immediate and hold while asserted
  assert property (@(posedge reset) count == 3'd0);
  assert property (cb reset |-> count == 3'd0);

  // Functional next-state checks (ignore cycles touching reset)
  // Up has priority over down (including when both are 1)
  assert property (cb (!reset && !$past(reset) && up)
                   |=> count == (($past(count)==3'd7) ? 3'd0 : $past(count)+3'd1));

  // Down only when up is 0
  assert property (cb (!reset && !$past(reset) && !up && down)
                   |=> count == (($past(count)==3'd0) ? 3'd7 : $past(count)-3'd1));

  // Hold when neither up nor down
  assert property (cb (!reset && !$past(reset) && !up && !down)
                   |=> count == $past(count));

  // Explicitly check both-high behaves like up (priority)
  assert property (cb (!reset && !$past(reset) && up && down)
                   |=> count == (($past(count)==3'd7) ? 3'd0 : $past(count)+3'd1));

  // Coverage: hit all states (out of reset)
  cover property (cb !reset && count==3'd0);
  cover property (cb !reset && count==3'd1);
  cover property (cb !reset && count==3'd2);
  cover property (cb !reset && count==3'd3);
  cover property (cb !reset && count==3'd4);
  cover property (cb !reset && count==3'd5);
  cover property (cb !reset && count==3'd6);
  cover property (cb !reset && count==3'd7);

  // Coverage: key behaviors
  cover property (cb (!reset && !$past(reset) && $past(count)==3'd7 && up) |=> count==3'd0); // up wrap
  cover property (cb (!reset && !$past(reset) && $past(count)==3'd0 && !up && down) |=> count==3'd7); // down wrap
  cover property (cb (!reset && !$past(reset) && !up && !down) |=> count==$past(count)); // idle hold
  cover property (cb (!reset && !$past(reset) && up && down)); // both-high seen

endmodule

// Bind to DUT
bind up_down_counter up_down_counter_sva sva_i (.*);