// SVA for module: calculator
module calculator_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic [7:0]  a,
  input  logic [7:0]  b,
  input  logic [1:0]  op,
  input  logic [7:0]  result,
  input  logic        valid
);

  // Reset behavior (synchronous)
  assert property (@(posedge clk) rst |=> (result == 8'h00 && valid == 1'b0))
    else $error("Reset: result/valid not cleared");

  // Functional checks (one-cycle latency), ignore cycles in reset
  assert property (@(posedge clk) disable iff (rst)
                   (op == 2'b00) |=> (valid && result == (a + b)[7:0]))
    else $error("ADD mismatch");

  assert property (@(posedge clk) disable iff (rst)
                   (op == 2'b01) |=> (valid && result == (a - b)[7:0]))
    else $error("SUB mismatch");

  assert property (@(posedge clk) disable iff (rst)
                   (op == 2'b10) |=> (valid && result == (a * b)[7:0]))
    else $error("MUL mismatch");

  assert property (@(posedge clk) disable iff (rst)
                   (op == 2'b11 && b == 8'h00) |=> (!valid && result == 8'h00))
    else $error("DIV by zero handling mismatch");

  assert property (@(posedge clk) disable iff (rst)
                   (op == 2'b11 && b != 8'h00) |=> (valid && result == (a / b)))
    else $error("DIV mismatch");

  // Outputs should never be X/Z outside reset
  assert property (@(posedge clk) disable iff (rst)
                   !$isunknown({result, valid}))
    else $error("result/valid X/Z detected");

  // Causality: any asserted valid must come from a legal prior-cycle condition
  assert property (@(posedge clk) disable iff (rst)
                   valid |-> ($past(!rst) && ($past(op) != 2'b11 || $past(b) != 8'h00)))
    else $error("valid asserted without legal prior op");

  // Coverage: ops, corner cases
  cover property (@(posedge clk) rst ##1 !rst); // reset release
  cover property (@(posedge clk) disable iff (rst) (op == 2'b00) ##1 valid);
  cover property (@(posedge clk) disable iff (rst) (op == 2'b01) ##1 valid);
  cover property (@(posedge clk) disable iff (rst) (op == 2'b10) ##1 valid);
  cover property (@(posedge clk) disable iff (rst) (op == 2'b11 && b == 8'h00) ##1 (!valid && result == 8'h00));
  cover property (@(posedge clk) disable iff (rst) (op == 2'b11 && b != 8'h00) ##1 (valid && result == (a / b)));

  // Arithmetic edge coverage
  cover property (@(posedge clk) disable iff (rst)
                  (op == 2'b00 && ($unsigned(a) + $unsigned(b)) > 8'hFF)); // add overflow
  cover property (@(posedge clk) disable iff (rst)
                  (op == 2'b01 && ($unsigned(a) < $unsigned(b))));         // sub underflow
  cover property (@(posedge clk) disable iff (rst)
                  (op == 2'b10 && ($unsigned(a) * $unsigned(b)) > 8'hFF)); // mul overflow

endmodule

// Bind into DUT
bind calculator calculator_sva u_calculator_sva (
  .clk(clk), .rst(rst), .a(a), .b(b), .op(op), .result(result), .valid(valid)
);