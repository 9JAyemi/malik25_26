// SVA for dffl_64: synchronous reset, load-enable DFF (64-bit)
// Bindable, concise, and covers functionality, priority, X-hygiene, and coverage.

module dffl_64_sva (
  input  logic        clk,
  input  logic        ld,
  input  logic        rst,
  input  logic [63:0] d,
  input  logic [63:0] q
);
  default clocking cb @(posedge clk); endclocking

  logic past_valid, init;
  initial begin past_valid = 1'b0; init = 1'b0; end
  always_ff @(posedge clk) begin
    past_valid <= 1'b1;
    if (rst || ld) init <= 1'b1;
  end

  // Functional correctness
  assert property (rst |=> q == 64'd0);
  assert property (disable iff (!past_valid) (!rst && ld)  |=> q == $past(d));
  assert property (disable iff (!past_valid) (!rst && !ld) |=> q == $past(q));

  // Priority: rst dominates ld
  assert property (rst && ld |=> q == 64'd0);

  // No spurious change: any change must be caused by rst or ld in prior cycle
  assert property (disable iff (!past_valid) (q != $past(q)) |-> $past(rst || ld));

  // X/Z hygiene
  assert property (disable iff (!past_valid) !$isunknown({rst, ld}));
  assert property (disable iff (!past_valid) (!rst && ld) |-> !$isunknown(d));
  assert property (disable iff (!init) !$isunknown(q));

  // Coverage (mode, priority, sequences, and key values)
  cover property (rst ##1 q == 64'd0);
  cover property (!rst && ld ##1 q == $past(d));
  cover property (!rst && !ld ##1 q == $past(q));
  cover property (rst && ld ##1 q == 64'd0);
  cover property (!rst && ld ##1 !rst && ld ##1 q == $past(d));
  cover property (!rst && ld && (d == 64'h0)                      ##1 q == $past(d));
  cover property (!rst && ld && (d == 64'hFFFF_FFFF_FFFF_FFFF)    ##1 q == $past(d));
endmodule

bind dffl_64 dffl_64_sva u_dffl_64_sva (.clk(clk), .ld(ld), .rst(rst), .d(d), .q(q));