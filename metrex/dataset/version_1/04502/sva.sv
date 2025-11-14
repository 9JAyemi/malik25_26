// SVA for top_module. Bind this file to the DUT.
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        control,
  input  logic [3:0]  a,
  input  logic [3:0]  b,
  input  logic [3:0]  out_add,
  input  logic [3:0]  out_sub,
  input  logic [7:0]  s,
  input  logic        overflow,
  input  logic [3:0]  reg_a,
  input  logic [3:0]  reg_b,
  input  logic [1:0]  state
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset behavior (no disable on this property)
  assert property (@(posedge clk) reset |-> (reg_a==4'h0 && reg_b==4'h0 && state==2'b00));

  // FSM next-state behavior
  assert property ((state==2'b00 && control)  |=> state==2'b01);
  assert property ((state==2'b00 && !control) |=> state==2'b00);
  assert property ((state==2'b01 && !control) |=> state==2'b00);
  assert property ((state==2'b01 && control)  |=> state==2'b01);

  // Functional correctness (end-to-end using registered inputs)
  assert property ((!reset && $past(!reset) && state==2'b00)
                   |-> out_add == (($past(a)+$past(b)) & 4'hF));
  assert property ((!reset && $past(!reset) && state==2'b01)
                   |-> out_sub == (($past(a)-$past(b)) & 4'hF));

  // S formatting
  assert property (state==2'b00 |-> s == {3'b000, 1'b0, out_add});
  assert property (state==2'b01 |-> s == {3'b000, 1'b0, out_sub});

  // Outputs stable when not driven in that state
  assert property (state==2'b00 |-> $stable(out_sub));
  assert property (state==2'b01 |-> $stable(out_add));

  // Overflow should be carry-out of 4-bit addition of registered inputs
  assert property ((!reset && $past(!reset))
                   |-> overflow == (( $past(a) + $past(b) ) > 4'hF));

  // Coverage
  cover property (state==2'b00);
  cover property (state==2'b01);
  cover property ((state==2'b00 && control) ##1 (state==2'b01));
  cover property ((state==2'b01 && !control) ##1 (state==2'b00));
  cover property ((!reset && $past(!reset)) && (( $past(a)+$past(b) ) > 4'hF)); // overflow case
  cover property (state==2'b01 && reg_b > reg_a); // subtraction borrow/wrap scenario

endmodule

bind top_module top_module_sva sva_inst (
  .clk(clk),
  .reset(reset),
  .control(control),
  .a(a),
  .b(b),
  .out_add(out_add),
  .out_sub(out_sub),
  .s(s),
  .overflow(overflow),
  .reg_a(reg_a),
  .reg_b(reg_b),
  .state(state)
);