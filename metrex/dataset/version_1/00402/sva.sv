// SVA bind module for top_module
module top_module_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        ena,
  input  logic [1:0]  shift_dir,
  input  logic [3:0]  sum,
  input  logic [3:0]  count,
  input  logic [3:0]  shifted_count
);
  default clocking cb @(posedge clk); endclocking

  // Track that we have at least one prior clock edge for $past usage
  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Basic X/knownness checks (concise but effective)
  // After first cycle, these should not be X
  assert property (past_valid |-> !$isunknown(shift_dir));
  assert property (past_valid |-> !$isunknown(sum));
  assert property (past_valid && !rst |-> !$isunknown(count));
  assert property (past_valid |-> !$isunknown(shifted_count));

  // Binary counter next-state behavior
  // Synchronous reset to 0
  assert property (rst |-> count == 4'h0);
  // Increment when enabled (no reset)
  assert property (past_valid && !rst && ena |-> count == $past(count) + 4'd1);
  // Hold when disabled (no reset)
  assert property (past_valid && !rst && !ena |-> count == $past(count));

  // Barrel shifter functional mapping (D is count)
  assert property (shift_dir == 2'b00 |-> shifted_count == count);
  assert property (shift_dir == 2'b01 |-> shifted_count == {count[2:0], 1'b0});
  assert property (shift_dir == 2'b10 |-> shifted_count == {1'b0, count[3:1]});
  assert property (shift_dir == 2'b11 |-> shifted_count == {count[2:0], count[3]});

  // Top-level sum functional mapping (end-to-end spec from count)
  assert property (shift_dir == 2'b00 |-> sum == (count + count));              // 2*count (mod 16)
  assert property (shift_dir == 2'b01 |-> sum == (count << 2));                 // count << 2 (mod 16)
  assert property (shift_dir == 2'b10 |-> sum == (count >> 2));                 // count >> 2
  assert property (shift_dir == 2'b11 |-> sum == {count[1:0], count[3:2]});     // rotate-left by 2

  // Lightweight coverage
  // Exercise each shift_dir with a nontrivial count
  cover property (past_valid && !rst && shift_dir == 2'b00 && count != 4'h0);
  cover property (past_valid && !rst && shift_dir == 2'b01 && count != 4'h0);
  cover property (past_valid && !rst && shift_dir == 2'b10 && count != 4'h0);
  cover property (past_valid && !rst && shift_dir == 2'b11 && count != 4'h0);

  // Cover counter wrap-around on enable
  cover property (past_valid && !rst && $past(!rst) && $past(ena) &&
                  $past(count) == 4'hF && count == 4'h0);

  // Cover hold behavior when disabled
  cover property (past_valid && !rst && !ena && count == $past(count));
endmodule

// Bind SVA to the DUT
bind top_module top_module_sva sva_i (
  .clk(clk),
  .rst(rst),
  .ena(ena),
  .shift_dir(shift_dir),
  .sum(sum),
  .count(count),
  .shifted_count(shifted_count)
)