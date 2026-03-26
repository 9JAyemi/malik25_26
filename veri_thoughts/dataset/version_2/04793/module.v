
module relational_module (
  input [(8 - 1):0] a,
  input [(8 - 1):0] b,
  output [(1 - 1):0] op,
  input clk,
  input ce,
  input clr
);

  // Declare internal wires and registers
  reg [(8 - 1):0] a_internal;
  reg [(8 - 1):0] b_internal;
  reg [(1 - 1):0] op_internal;

  // Assign inputs to internal wires
  always @(posedge clk or posedge clr) begin
    if (clr) begin
      a_internal <= 0;
      b_internal <= 0;
    end else begin
      a_internal <= a;
      b_internal <= b;
    end
  end

  // Compare inputs and update output when enable signal is high
  always @(posedge clk) begin
    if (ce) begin
      op_internal <= (a_internal == b_internal);
    end
  end

  // Assign internal output to module output
  assign op = op_internal;

endmodule