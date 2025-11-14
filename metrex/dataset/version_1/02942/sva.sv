// SVA for max_value
// Bind this checker and connect clk to any suitable sampling clock.

module max_value_sva #(parameter int WIDTH = 5)
(
  input logic clk,
  input logic [WIDTH-1:0] a,
  input logic [WIDTH-1:0] b,
  input logic [WIDTH-1:0] result
);
  default clocking @(posedge clk); endclocking

  // Sanity: no X/Z on critical signals
  ap_no_x: assert property (!$isunknown({a,b,result}))
    else $error("max_value: X/Z detected on inputs/outputs");

  // Functional correctness: result must be the max(a,b)
  ap_max: assert property (result == ((a >= b) ? a : b))
    else $error("max_value: result != max(a,b)");

  // Functional coverage
  cp_a_gt_b: cover property (a > b  && result == a);
  cp_b_gt_a: cover property (a < b  && result == b);
  cp_eq:     cover property (a == b && result == a);

  localparam logic [WIDTH-1:0] MIN = '0;
  localparam logic [WIDTH-1:0] MAX = {WIDTH{1'b1}};
  cp_min_max: cover property (a == MIN && b == MAX && result == b);
  cp_max_min: cover property (a == MAX && b == MIN && result == a);
  cp_min_eq:  cover property (a == MIN && b == MIN && result == MIN);
  cp_max_eq:  cover property (a == MAX && b == MAX && result == MAX);
endmodule

bind max_value max_value_sva #(.WIDTH(5))
  i_max_value_sva (.clk(clk), .a(a), .b(b), .result(result));