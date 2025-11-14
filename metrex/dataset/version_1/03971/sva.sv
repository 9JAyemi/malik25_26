// SVA for square_wave
// Bindable checker that reaches inside to observe internal state
module square_wave_sva (
  input logic clk,
  input logic reset,
  input logic out,
  input logic [1:0] state
);

  // Basic sanity: no X/Z when not in reset
  assert property (@(posedge clk) !reset |-> (!$isunknown(state) && !$isunknown(out)));

  // Synchronous reset effect and hold
  assert property (@(posedge clk) reset |=> (state==2'b00 && out==1'b0));
  assert property (@(posedge clk) (reset && $past(reset)) |-> (state==2'b00 && out==1'b0 && $stable(state) && $stable(out)));

  // Next-state transitions (one-hot progression 00->01->10->11->00)
  assert property (@(posedge clk) disable iff (reset) (state==2'b00) |=> (state==2'b01));
  assert property (@(posedge clk) disable iff (reset) (state==2'b01) |=> (state==2'b10));
  assert property (@(posedge clk) disable iff (reset) (state==2'b10) |=> (state==2'b11));
  assert property (@(posedge clk) disable iff (reset) (state==2'b11) |=> (state==2'b00));

  // Output correctness (out on next cycle is a function of current state)
  assert property (@(posedge clk) disable iff (reset) (state inside {2'b00,2'b11}) |=> (out==1'b0));
  assert property (@(posedge clk) disable iff (reset) (state inside {2'b01,2'b10}) |=> (out==1'b1));

  // Period-4 behavior (guarded from reset interference)
  assert property (@(posedge clk)
    (!reset && !$past(reset,1) && !$past(reset,2) && !$past(reset,3) && !$past(reset,4))
    |-> (state==$past(state,4) && out==$past(out,4)));

  // 2-cycle anti-correlation (out alternates every 2 cycles)
  assert property (@(posedge clk)
    (!reset && !$past(reset,1) && !$past(reset,2)) |-> (out != $past(out,2)));

  // Coverage: full state cycle
  cover property (@(posedge clk) disable iff (reset)
    (state==2'b00 ##1 state==2'b01 ##1 state==2'b10 ##1 state==2'b11 ##1 state==2'b00));

  // Coverage: output pattern 0,1,1,0
  cover property (@(posedge clk) disable iff (reset)
    (out==1'b0 ##1 out==1'b1 ##1 out==1'b1 ##1 out==1'b0));

endmodule

// Bind into the DUT (accesses internal 'state')
bind square_wave square_wave_sva sva_i (.*);