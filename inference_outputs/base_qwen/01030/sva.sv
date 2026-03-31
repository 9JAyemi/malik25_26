```systemverilog
module constant_generator_sva (
  input logic clk,
  input logic ce,
  input logic clr,
  output logic op
);
  reg op_reg;

  always @(posedge clk) begin
    if (clr) begin
      op_reg <= 1'b0;
    end else if (ce) begin
      op_reg <= 1'b1;
    end
  end

  assign op = op_reg;

  ///// Sequential logic rules /////
  // op_reg can only transition from 0 to 1 when ce is HIGH and clr is LOW.
  transition_1: assert property (
    @(posedge clk) disable iff (!clr) $rose(op_reg) |-> (ce == 1'b1)
  );
  // op_reg can only transition from 1 to 0 when clr is HIGH.
  transition_2: assert property (
    @(posedge clk) disable iff (!clr) $fell(op_reg) |-> (clr == 1'b1)
  );
  // op_reg can only transition from 0 to 0 when ce is LOW and clr is LOW.
  transition_3: assert property (
    @(posedge clk) disable iff (!clr) $fell(op_reg) |-> (ce == 1'b0)
  );
  // op_reg can only transition from 1 to 1 when ce is HIGH and clr is LOW.
  transition_4: assert property (
    @(posedge clk) disable iff (!clr) $rose(op_reg) |-> (ce == 1'b1)
  );
  // op_reg is always 0 when clr is HIGH.
  reset_1: assert property (
    @(posedge clk) !clr |-> op_reg == 1'b0
  );
  // op_reg is always 1 when ce is HIGH and clr is LOW.
  set_1: assert property (
    @(posedge clk) disable iff (!clr) (ce == 1'b1) |-> op_reg == 1'b1
  );
  // op_reg is always 0 when ce is LOW and clr is LOW.
  clear_1: assert property (
    @(posedge clk) disable iff (!clr) (ce == 1'b0) |-> op_reg == 1'b0
  );
  // op_reg is always 1 when ce is HIGH and clr is LOW.
  set_2: assert property (
    @(posedge clk) disable iff (!clr) (ce == 1'b1) |-> op_reg == 1'b1
  );
  // op_reg is always 0 when ce is LOW and clr is LOW.
  clear_2: assert property (
    @(posedge clk) disable iff (!clr) (ce == 1'b0) |-> op_reg == 1'b0
  );
endmodule
```