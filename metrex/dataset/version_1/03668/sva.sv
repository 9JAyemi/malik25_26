// SVA for binary_stack
// Bind module
module binary_stack_sva #(parameter int dw=8, parameter int stack_size=8)
(
  input  logic                     clk,
  input  logic                     rst,
  input  logic                     push_i,
  input  logic                     pop_i,
  input  logic [dw-1:0]            data_i,
  input  logic [dw-1:0]            data_o,
  input  logic                     empty_o,
  input  logic [$clog2(stack_size+1)-1:0] top,
  input  var  logic [dw-1:0]       stack [0:stack_size-1]
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior (synchronous reset)
  assert property (rst |=> top == 0);

  // Invariants
  assert property (top <= stack_size);
  assert property (empty_o == (top == 0));
  assert property (data_o == ((top > 0) ? stack[top-1] : '0));

  // Helper lets (use $past-sampled request/level)
  let acc_push = $past(push_i) && ($past(top) < stack_size);
  let acc_pop  = (!acc_push) && $past(pop_i) && ($past(top) > 0);

  // Push accepted: pointer increments, memory write, data_o reflects new top
  assert property (disable iff (rst)
                   acc_push |-> (top == $past(top)+1) &&
                               (stack[$past(top)] == $past(data_i)) &&
                               (data_o == $past(data_i)));

  // Pop accepted: pointer decrements, data_o reflects previous next item (or 0)
  assert property (disable iff (rst)
                   acc_pop |-> (top == $past(top)-1) &&
                              (data_o == (($past(top) > 1)
                                          ? $past(stack[$past(top)-2]) : '0)));

  // No accepted operation: pointer stable
  assert property (disable iff (rst)
                   (!acc_push && !acc_pop) |-> (top == $past(top)));

  // Priority/edge cases
  // Both asserted mid (0 < top < stack_size): push wins
  assert property (disable iff (rst)
                   $past(push_i) && $past(pop_i) &&
                   ($past(top) > 0) && ($past(top) < stack_size)
                   |-> (top == $past(top)+1) && (data_o == $past(data_i)));

  // Both asserted at full: pop occurs
  assert property (disable iff (rst)
                   $past(push_i) && $past(pop_i) && ($past(top) == stack_size)
                   |-> (top == stack_size-1));

  // Push when full without pop: no change
  assert property (disable iff (rst)
                   $past(push_i) && !$past(pop_i) && ($past(top) >= stack_size)
                   |-> (top == $past(top)));

  // Pop when empty without push: no change
  assert property (disable iff (rst)
                   $past(pop_i) && !$past(push_i) && ($past(top) == 0)
                   |-> (top == $past(top)));

  // Functional coverage
  cover property (rst);
  cover property (disable iff (rst) acc_push);
  cover property (disable iff (rst) acc_pop);
  cover property (disable iff (rst) top == stack_size);
  cover property (disable iff (rst) top == 0);
  cover property (disable iff (rst)
                  $past(push_i) && !$past(pop_i) && ($past(top) >= stack_size)); // push@full
  cover property (disable iff (rst)
                  $past(pop_i) && !$past(push_i) && ($past(top) == 0));         // pop@empty
  cover property (disable iff (rst)
                  $past(push_i) && $past(pop_i) &&
                  ($past(top) > 0) && ($past(top) < stack_size));               // simult mid
  cover property (disable iff (rst)
                  $past(push_i) && $past(pop_i) && ($past(top) == stack_size)); // simult full
endmodule

// Bind to DUT (connect internals top/stack explicitly)
bind binary_stack binary_stack_sva #(.dw(dw), .stack_size(stack_size)) bsva
(
  .clk(clk), .rst(rst), .push_i(push_i), .pop_i(pop_i),
  .data_i(data_i), .data_o(data_o), .empty_o(empty_o),
  .top(top), .stack(stack)
);