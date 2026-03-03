// SVA for bitwise_operations
// Concise, high-quality checks + focused functional coverage.
// Provide a clock from your TB when binding.

module bitwise_operations_sva #(parameter bit USE_RESET = 0) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic [1:0]  operation_select,
  input  logic [4:0]  shift_amount,
  input  logic [31:0] result
);
  default clocking cb @(posedge clk); endclocking
  wire dis = USE_RESET ? !rst_n : 1'b0;

  // Control sanity (avoid X/Z on control)
  assert property (disable iff (dis) !$isunknown(operation_select));
  assert property (disable iff (dis) !$isunknown(shift_amount));

  // No X on result when all inputs are known
  assert property (disable iff (dis)
    !$isunknown({a,b,operation_select,shift_amount}) |-> !$isunknown(result));

  // Functional equivalence of the combinational select (single golden check)
  assert property (disable iff (dis)
    result === (operation_select==2'b00 ? (a & b) :
                operation_select==2'b01 ? (a | b) :
                operation_select==2'b10 ? (a ^ b) :
                                          (a << shift_amount)));

  // Stability: if inputs and select are stable, result must be stable
  assert property (disable iff (dis)
    $stable({a,b,operation_select,shift_amount}) |-> $stable(result));

  // Functional coverage: each operation selected
  cover property (disable iff (dis) operation_select==2'b00);
  cover property (disable iff (dis) operation_select==2'b01);
  cover property (disable iff (dis) operation_select==2'b10);
  cover property (disable iff (dis) operation_select==2'b11);

  // Corner coverage: shift extremes and key data patterns
  cover property (disable iff (dis) operation_select==2'b11 && shift_amount==5'd0);
  cover property (disable iff (dis) operation_select==2'b11 && shift_amount==5'd31);
  cover property (disable iff (dis) operation_select==2'b10 && a==b);                // XOR->0
  cover property (disable iff (dis) operation_select inside {2'b00,2'b01,2'b10} &&
                                   a==32'h0 && b==32'h0);
  cover property (disable iff (dis) operation_select inside {2'b00,2'b01,2'b10} &&
                                   a==32'hFFFF_FFFF && b==32'hFFFF_FFFF);
endmodule

// Example bind (provide a TB clock 'clk'; tie rst_n as needed)
bind bitwise_operations bitwise_operations_sva sva_u (
  .clk(clk), .rst_n(1'b1),
  .a(a), .b(b), .operation_select(operation_select),
  .shift_amount(shift_amount), .result(result)
);