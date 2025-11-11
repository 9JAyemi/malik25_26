// SVA for counter: concise, high-quality checks and key coverage
module counter_sva (
  input logic       clk,
  input logic       reset,
  input logic [3:0] value
);

  default clocking cb @(posedge clk); endclocking

  // Sanity
  assert property (@cb !$isunknown(reset));
  assert property (@cb !$isunknown(value));

  // Value changes only on clk or async reset edge
  assert property ( $changed(value) |-> ($rose(clk) || $rose(reset)) );

  // Async reset clears immediately (same timestep)
  assert property (@(posedge reset) ##0 (value == 4'h0));

  // While reset is high, value must be 0
  assert property (@cb reset |-> (value == 4'h0));

  // First clk after reset deasserts: 0 -> 1
  assert property (@cb $past(reset) && !reset |-> (value == 4'h1));

  // Normal counting when not in or just out of reset
  assert property (@cb !reset && !$past(reset)
                   |-> value == (($past(value) == 4'hF) ? 4'h0 : $past(value) + 4'h1));

  // Explicit wrap check at 0xF
  assert property (@cb !reset && !$past(reset) && ($past(value) == 4'hF) |-> (value == 4'h0));

  // Key coverage
  cover property (@(posedge reset) 1);                        // see a reset
  cover property (@cb $past(reset) && !reset && value==4'h1); // post-reset increment
  cover property (@cb !reset && $past(!reset) && $past(value)==4'hE && value==4'hF); // near-wrap
  cover property (@cb !reset && $past(!reset) && $past(value)==4'hF && value==4'h0); // wrap

endmodule

// Example bind (uncomment and adjust instance path as needed):
// bind counter counter_sva u_counter_sva (.*);