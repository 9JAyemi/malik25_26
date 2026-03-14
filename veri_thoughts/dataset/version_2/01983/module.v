module mult_module(
  input clk,
  input reset,
  input [7:0] in1,
  input [7:0] in2,
  output reg [15:0] out
);

  always @(posedge clk) begin
    if (reset) begin
      out <= 0;
    end else begin
      out <= in1 * in2;
    end
  end

endmodule

module lower8bits(
  input clk,
  input [15:0] in,
  output reg [7:0] out_lo
);

  always @(posedge clk) begin
    out_lo <= in[7:0];
  end

endmodule

module mult_system(
  input clk,
  input reset,
  input [7:0] in1,
  input [7:0] in2,
  output reg [15:0] out,
  output reg [7:0] out_lo
);

  wire [15:0] mult_result;
  mult_module mult_inst(
    .clk(clk),
    .reset(reset),
    .in1(in1),
    .in2(in2),
    .out(mult_result)
  );

  lower8bits lower_inst(
    .clk(clk),
    .in(mult_result),
    .out_lo(out_lo)
  );

  always @(posedge clk) begin
    if (reset) begin
      out <= 0;
    end else begin
      out <= mult_result;
    end
  end

endmodule