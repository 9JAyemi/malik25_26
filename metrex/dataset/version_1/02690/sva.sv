// SVA for top_module
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  a,
  input  logic [7:0]  b,
  input  logic [7:0]  q,
  input  logic        greater_than,
  input  logic        equal,
  input  logic        enable,
  input  logic [3:0]  count,
  input  logic [7:0]  sum
);
  default clocking cb @(posedge clk); endclocking

  // track valid past-sample for $past usage
  logic past_valid;
  always_ff @(posedge clk) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // X checks (post-reset)
  assert property (disable iff (reset) !$isunknown({greater_than,equal,enable,count,sum,q}));

  // Comparator correctness
  assert property (greater_than == (a > b));

  // Control-logic correctness and cross-consistency
  assert property (equal  == (a == b));
  assert property (enable == (a >= b));
  assert property (!(greater_than && equal));
  assert property (enable == (greater_than || equal));

  // Counter behavior
  assert property (reset |=> count == 4'd0);
  assert property (disable iff (reset) past_valid && enable   |=> count == ($past(count) + 4'd1));
  assert property (disable iff (reset) past_valid && !enable  |=> count ==  $past(count));

  // Functional module behavior
  assert property (sum == ({7'b0, a[0]} + count));

  // Top-level q behavior (priority mux)
  assert property (reset |=> q == 8'd0);
  assert property (disable iff (reset) past_valid && greater_than             |=> q == {4'b0, $past(count)});
  assert property (disable iff (reset) past_valid && (!greater_than && equal) |=> q == $past(sum));
  assert property (disable iff (reset) past_valid && (!greater_than && !equal)|=> q == $past(a));

  // Coverage
  cover property (reset ##1 q == 8'd0);
  cover property (disable iff (reset) greater_than);
  cover property (disable iff (reset) (!greater_than && equal));
  cover property (disable iff (reset) (!greater_than && !equal));
  cover property (disable iff (reset) past_valid && greater_than ##1 q == {4'b0, $past(count)});
  cover property (disable iff (reset) past_valid && (!greater_than && equal) ##1 q == $past(sum));
  cover property (disable iff (reset) past_valid && (!greater_than && !equal) ##1 q == $past(a));
  cover property (disable iff (reset) past_valid && $past(enable) && ($past(count)==4'hF) ##1 (count==4'h0)); // wrap
  cover property (disable iff (reset) !enable ##1 enable); // enable rise
  cover property (disable iff (reset) enable ##1 !enable); // enable fall
  cover property (sum == 8'h10); // a[0]=1 and count=15 case
endmodule

bind top_module top_module_sva sva_top (
  .clk         (clk),
  .reset       (reset),
  .a           (a),
  .b           (b),
  .q           (q),
  .greater_than(greater_than),
  .equal       (equal),
  .enable      (enable),
  .count       (count),
  .sum         (sum)
);