// SVA bind module for arithmetic_module
module arithmetic_module_sva #(parameter WIDTH=32)
(
  input  logic                 clk,
  input  logic                 rst_n,
  input  logic [1:0]           op,
  input  logic [WIDTH-1:0]     a,
  input  logic [WIDTH-1:0]     b,
  input  logic [WIDTH-1:0]     out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Helpers
  let known_inputs = !$isunknown({op,a,b});
  let e_add = (a + b)[WIDTH-1:0];
  let e_sub = (a - b)[WIDTH-1:0];
  let e_mul = (a * b)[WIDTH-1:0];

  // Functional correctness
  assert property (known_inputs && (op == 2'b00) |-> out == e_add);
  assert property (known_inputs && (op == 2'b01) |-> out == e_sub);
  assert property (known_inputs && (op == 2'b10) |-> out == e_mul);
  assert property (known_inputs && (op == 2'b11) && (b != '0) |-> out == (a / b));

  // Division-by-zero behavior: output should be unknown
  assert property (known_inputs && (op == 2'b11) && (b == '0) |-> $isunknown(out));

  // Out must be known whenever inputs are known and not div-by-zero
  assert property (known_inputs && !((op == 2'b11) && (b == '0)) |-> !$isunknown(out));

  // Basic op-code coverage
  cover property (known_inputs && (op == 2'b00));
  cover property (known_inputs && (op == 2'b01));
  cover property (known_inputs && (op == 2'b10));
  cover property (known_inputs && (op == 2'b11));

  // Corner-case coverage
  // add overflow carry out
  cover property (known_inputs && (op == 2'b00) && (({1'b0,a}+{1'b0,b})[WIDTH] == 1'b1));
  // sub borrow (unsigned underflow)
  cover property (known_inputs && (op == 2'b01) && (a < b));
  // mul overflow (upper product bits non-zero)
  cover property (known_inputs && (op == 2'b10) && (((a*b) >> WIDTH) != '0));
  // div with remainder
  cover property (known_inputs && (op == 2'b11) && (b != '0) && ((a % b) != '0));
  // div-by-zero exercised
  cover property (known_inputs && (op == 2'b11) && (b == '0));
endmodule

// Example bind (requires clk and rst_n visible where bind is elaborated)
bind arithmetic_module arithmetic_module_sva #(.WIDTH(WIDTH))
  u_sva (.clk(clk), .rst_n(rst_n), .op(op), .a(a), .b(b), .out(out));