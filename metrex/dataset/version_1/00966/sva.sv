// SVA for counter: concise, high-quality checks and coverage
module counter_sva (
  input logic        clk,
  input logic        rst,
  input logic        ctrl,
  input logic        load,
  input logic [15:0] load_val,
  input logic [15:0] count
);
  default clocking cb @ (posedge clk); endclocking

  // Guard $past() on first cycle
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Basic 2-state checks
  assert property (!$isunknown({rst, load, ctrl}));
  assert property (!$isunknown(count));
  assert property (load |-> !$isunknown(load_val));

  // Priority/functional behavior
  assert property (rst |-> count == 16'd0);
  assert property (!rst && load |-> count == load_val);
  assert property (!rst && !load && ctrl  |-> count == ($past(count) + 16'd1));
  assert property (!rst && !load && !ctrl |-> count == ($past(count) - 16'd1));

  // Coverage: each mode and wraparounds
  cover property (rst);
  cover property (!rst && load);
  cover property (!rst && !load && ctrl);
  cover property (!rst && !load && !ctrl);
  cover property (!rst && !load && ctrl  && $past(count)==16'hFFFF && count==16'h0000); // up-wrap
  cover property (!rst && !load && !ctrl && $past(count)==16'h0000 && count==16'hFFFF); // down-wrap
endmodule

bind counter counter_sva u_counter_sva (.*);