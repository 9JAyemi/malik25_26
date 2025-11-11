// SVA for up_down_counter: concise, priority-aware, full functional checks + key coverage

module up_down_counter_sva (
  input  logic        clk,
  input  logic        reset,     // sync active-high
  input  logic        load,      // no-op per RTL
  input  logic        up_down,   // 1: up, 0: down
  input  logic [15:0] q
);

  default clocking cb @(posedge clk); endclocking

  // track we have a prior cycle for $past
  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // 16-bit modulo helpers
  function automatic logic [15:0] plus1 (input logic [15:0] a);
    plus1 = (a + 16'h0001) & 16'hFFFF;
  endfunction
  function automatic logic [15:0] minus1 (input logic [15:0] a);
    minus1 = (a - 16'h0001) & 16'hFFFF;
  endfunction

  // Reset behavior (synchronous)
  assert property (cb reset |=> q == 16'h0000);

  // Count behavior with correct priority: reset > load > up/down
  assert property (cb past_valid && $past(!reset && load)
                   |-> q == $past(q));                       // load holds (per RTL)

  assert property (cb past_valid && $past(!reset && !load && up_down)
                   |-> q == plus1($past(q)));                // count up

  assert property (cb past_valid && $past(!reset && !load && !up_down)
                   |-> q == minus1($past(q)));               // count down

  // Explicit priority when load and up_down both high: load wins (hold)
  assert property (cb past_valid && $past(!reset && load && up_down)
                   |-> q == $past(q));

  // No combinational glitches on q (sequential-only updates)
  assert property (@(negedge clk) !$changed(q));

  // q should never be X/Z after first clock
  assert property (cb past_valid |-> !$isunknown(q));

  // Functional coverage
  cover property (cb reset);                                        // reset seen
  cover property (cb !reset && load);                               // load seen
  cover property (cb !reset && !load && up_down);                   // up step seen
  cover property (cb !reset && !load && !up_down);                  // down step seen

  // Priority combinations
  cover property (cb reset && load);                                // reset dominates load
  cover property (cb !reset && load && up_down);                    // load dominates up/down

  // Wrap-around coverage
  cover property (cb past_valid && $past(!reset && !load && up_down && ($past(q)==16'hFFFF))
                   ##1 (q==16'h0000));                              // up wrap
  cover property (cb past_valid && $past(!reset && !load && !up_down && ($past(q)==16'h0000))
                   ##1 (q==16'hFFFF));                              // down wrap

  // Back-to-back direction change
  cover property (cb !reset && !load && up_down ##1 !reset && !load && !up_down);

endmodule

// Bind assertions to all instances of up_down_counter
bind up_down_counter up_down_counter_sva sva_i (
  .clk(clk),
  .reset(reset),
  .load(load),
  .up_down(up_down),
  .q(q)
);