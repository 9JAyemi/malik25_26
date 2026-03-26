
module my_module (
  input in0,
  input in1,
  input in2,
  input in3,
  input d0,
  input d1,
  input d2,
  input d3,
  input clk,
  input reset,
  output reg out0,
  output reg out1,
  output out2,
  output out3
);

  wire mux_d2_out;
  wire mux_d3_out;
  wire nor_d2_out;
  wire nor_d3_out;

  // Mux for d2
  mux2x1 mux_d2 (
    .a(in0),
    .b(in1),
    .s(d2),
    .y(mux_d2_out)
  );

  // Mux for d3
  mux2x1 mux_d3 (
    .a(in2),
    .b(in3),
    .s(d3),
    .y(mux_d3_out)
  );

  // NOR for d2
  nor2x1 nor_d2 (
    .a(reset),
    .b(mux_d2_out),
    .y(nor_d2_out)
  );

  // DFF for d2
  dffposx1 dff_d2 (
    .d(nor_d2_out),
    .clk(clk),
    .q(out2)
  );

  // NOR for d3
  nor2x1 nor_d3 (
    .a(reset),
    .b(mux_d3_out),
    .y(nor_d3_out)
  );

  // DFF for d3
  dffposx1 dff_d3 (
    .d(mux_d3_out),
    .clk(clk),
    .q(out3)
  );

  // Assign out0 and out1
  always @(*) begin
    out0 = d0 ? in1 : in0;
    out1 = d1 ? in3 : in2;
  end

endmodule
module mux2x1(
    input a,
    input b,
    input s,
    output y
);

assign y = s ? b : a;

endmodule
module nor2x1(
    input a,
    input b,
    output y
);

assign y = ~(a | b);

endmodule
module dffposx1(
    input d,
    input clk,
    output reg q
);

always @(posedge clk) begin
    q <= d;
end

endmodule