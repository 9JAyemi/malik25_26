module top_module (
  input clk,
  input reset, // Synchronous active-high reset
  input [7:0] in1,
  input [7:0] in2,
  input select,
  output [7:0] out
);

  wire [7:0] adder1_out;
  wire [7:0] adder2_out;
  wire [7:0] and_out;

  // Instantiate the two adder modules
  adder adder1 (
    .clk(clk),
    .reset(reset),
    .in1(in1),
    .in2(in2),
    .out(adder1_out)
  );

  adder adder2 (
    .clk(clk),
    .reset(reset),
    .in1(in1),
    .in2(in2),
    .out(adder2_out)
  );

  // Instantiate the control logic module
  control_logic control (
    .select(select),
    .adder1_out(adder1_out),
    .adder2_out(adder2_out),
    .and_out(and_out)
  );

  // Output the result of the AND operation
  assign out = and_out;

endmodule

module adder (
  input clk,
  input reset, // Synchronous active-high reset
  input [7:0] in1,
  input [7:0] in2,
  output [7:0] out
);

  reg [7:0] sum;

  always @(posedge clk) begin
    if (reset) begin
      sum <= 8'd0;
    end else begin
      sum <= in1 + in2;
    end
  end

  assign out = sum;

endmodule

module control_logic (
  input select,
  input [7:0] adder1_out,
  input [7:0] adder2_out,
  output [7:0] and_out
);

  assign and_out = (select) ? (adder1_out & adder2_out) : (adder2_out & adder1_out);

endmodule