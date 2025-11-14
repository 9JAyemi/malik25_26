// SVA for simple_calculator
module simple_calculator_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        ce,
  input  logic [7:0]  a,
  input  logic [7:0]  b,
  input  logic [1:0]  op,
  input  logic [7:0]  result
);
  localparam logic [1:0] ADD = 2'b00;
  localparam logic [1:0] SUB = 2'b01;

  // Reset behavior
  property p_reset_clears; @(posedge clk) reset |=> (result == 8'h00); endproperty
  property p_reset_holds_zero; @(posedge clk) (reset && $past(reset)) |-> (result == 8'h00); endproperty
  assert property (p_reset_clears);
  assert property (p_reset_holds_zero);

  // No Xs
  assert property (@(posedge clk) disable iff (reset) !$isunknown(result));
  assert property (@(posedge clk) disable iff (reset) ce |-> !$isunknown({a,b,op,ce}));

  // Valid op when enabled
  assert property (@(posedge clk) disable iff (reset) ce |-> (op inside {ADD,SUB}));

  // Functional correctness (1-cycle latency, 8-bit wrap)
  assert property (@(posedge clk) disable iff (reset)
                   (ce && (op==ADD)) |=> (result == (($past(a)+$past(b)) & 8'hFF)));
  assert property (@(posedge clk) disable iff (reset)
                   (ce && (op==SUB)) |=> (result == (($past(a)-$past(b)) & 8'hFF)));

  // Hold when ce==0
  assert property (@(posedge clk) disable iff (reset) !ce |=> (result == $past(result)));

  // Any change must be caused by prior ce or reset
  assert property (@(posedge clk) (result != $past(result)) |-> ($past(ce) || $past(reset)));

  // Coverage
  cover property (@(posedge clk) disable iff (reset) (ce && op==ADD));
  cover property (@(posedge clk) disable iff (reset) (ce && op==SUB));
  cover property (@(posedge clk) disable iff (reset) (ce && op==ADD && ({1'b0,a}+{1'b0,b})[8])); // add overflow
  cover property (@(posedge clk) disable iff (reset) (ce && op==SUB && (a < b)));               // sub underflow
  cover property (@(posedge clk) disable iff (reset) (!ce ##1 (!ce && (result==$past(result))))); // hold across 2 cycles
  cover property (@(posedge clk) disable iff (reset) (ce && op==ADD) ##1 (ce && op==SUB));       // back-to-back ops
  cover property (@(posedge clk) reset ##1 (result==8'h00));                                      // reset clear observed

endmodule

// Bind into DUT (adjust instance pathing as needed)
bind simple_calculator simple_calculator_sva sva_i (
  .clk(clk),
  .reset(reset),
  .ce(ce),
  .a(a),
  .b(b),
  .op(op),
  .result(result)
);