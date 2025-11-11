// SVA for the simple arithmetic design
// Concise, high-quality checks with essential coverage

// ---------------- adder ----------------
module adder_sva (input logic [3:0] a, b, input logic [3:0] sum);
  // Functional correctness and X-prop
  a_add_correct: assert property (@(*)
    sum == ($unsigned(a) + $unsigned(b))[3:0]
  );
  a_add_no_x:    assert property (@(*)
    !$isunknown({a,b}) |-> !$isunknown(sum)
  );

  // Key coverage
  c_add_overflow: cover property (@(*)
    ($unsigned(a)+$unsigned(b)) > 15
  );
  c_add_zero:     cover property (@(*)
    (a==4'd0 && b==4'd0 && sum==4'd0)
  );
endmodule
bind adder adder_sva(.a(a), .b(b), .sum(sum));

// -------------- multiplier --------------
module multiplier_sva (input logic [3:0] a, b, input logic [7:0] product);
  // Functional correctness and X-prop
  a_mul_correct: assert property (@(*)
    product == ($unsigned(a) * $unsigned(b))
  );
  a_mul_no_x:    assert property (@(*)
    !$isunknown({a,b}) |-> !$isunknown(product)
  );

  // Key coverage
  c_mul_zero: cover property (@(*)
    (a==0 || b==0) && product==0
  );
  c_mul_max:  cover property (@(*)
    (a==4'd15 && b==4'd15 && product==8'd225)
  );
endmodule
bind multiplier multiplier_sva(.a(a), .b(b), .product(product));

// ------------- final_module -------------
module final_module_sva (input logic [3:0] sum,
                         input logic [7:0] product,
                         input logic [7:0] final_output);
  // Functional correctness and X-prop
  a_final_correct: assert property (@(*)
    final_output == ((($unsigned(sum) << 1) + ($unsigned(product) >> 1)) & 8'hFF)
  );
  a_final_no_x:    assert property (@(*)
    !$isunknown({sum,product}) |-> !$isunknown(final_output)
  );

  // Key coverage: exercise /2 truncation and boundary
  c_final_div_odd: cover property (@(*)
    product[0] == 1'b1
  );
  c_final_sum_max: cover property (@(*)
    sum == 4'd15
  );
endmodule
bind final_module final_module_sva(.sum(sum), .product(product), .final_output(final_output));

// --------------- top_module ---------------
module top_module_sva (
  input logic        clk, reset,
  input logic [3:0]  a, b,
  input logic [3:0]  sum, sum_wire,
  input logic [7:0]  product, product_wire, final_output
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Connectivity checks
  a_conn_sum:     assert property (sum     == sum_wire);
  a_conn_product: assert property (product == product_wire);

  // End-to-end functional check from top-level inputs
  a_end_to_end: assert property (
    final_output == (
      ((($unsigned(a)+$unsigned(b))[3:0]) << 1) +
      (($unsigned(a)*$unsigned(b)) >> 1)
    )[7:0]
  );

  // No-X propagation at top level
  a_top_no_x: assert property (
    !$isunknown({a,b}) |-> !$isunknown({sum,product,final_output})
  );

  // System-level coverage: overflow in sum, odd product, extreme multiply
  c_top_sum_overflow: cover property (
    ($unsigned(a)+$unsigned(b)) > 15
  );
  c_top_mul_odd:      cover property (
    (($unsigned(a)*$unsigned(b)) & 8'h01) == 1'b1
  );
  c_top_15x15:        cover property (
    a==4'd15 && b==4'd15
  );
endmodule
bind top_module top_module_sva(
  .clk(clk), .reset(reset),
  .a(a), .b(b),
  .sum(sum), .sum_wire(sum_wire),
  .product(product), .product_wire(product_wire),
  .final_output(final_output)
);