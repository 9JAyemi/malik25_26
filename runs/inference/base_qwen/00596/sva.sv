module inverter_sva (
  input logic ip,
  input logic op,
  input logic clk,
  input logic ce,
  input logic clr
);
  // Inverter logic must be enabled by ce
  enable_ce: assert property (
    @(posedge clk) disable iff (!clr) ce |-> op_reg == ~ip
  );

  // op_reg should only change on the positive edge of clk when ce is high
  reg_change: assert property (
    @(posedge clk) disable iff (!clr) ce |-> op_reg == ~ip
  );

  // op should be cleared when clr is high
  clear_op: assert property (
    @(posedge clk) disable iff (!clr) clr |-> op == 1'b0
  );

  // op should be the value of op_reg when clr is low
  op_value: assert property (
    @(posedge clk) disable iff (!clr) !clr |-> op == op_reg
  );

endmodule