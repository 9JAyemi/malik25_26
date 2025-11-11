
module Pipeline #(
  parameter n = 4, // number of input signals
  parameter m = 2, // number of output signals
  parameter p = 3  // number of pipeline stages
) (
  input [n-1:0] in,
  output [m-1:0] out,
  input clk
);

  wire [n-1:0] stage0_out; // output of stage 0
  wire [n-1:0] stage1_out; // output of stage 1
  wire [n-1:0] stage2_out; // output of stage 2

  // instantiate pipeline stages
  Stage0 #(.n(n)) stage0(
    .in(in),
    .out(stage0_out),
    .clk(clk)
  );

  Stage1 #(.n(n)) stage1(
    .in(stage0_out),
    .out(stage1_out),
    .clk(clk)
  );

  Stage2 #(.n(n)) stage2(
    .in(stage1_out),
    .out(stage2_out),
    .clk(clk)
  );


  // output signals are the final output of the last stage of the pipeline
  assign out = stage2_out[m-1:0];

endmodule
module Stage0 #(
  parameter n = 4
) (
  input [n-1:0] in,
  output [n-1:0] out,
  input clk
);

  reg [n-1:0] reg_out; // pipeline register

  // perform computation in this stage
  assign out = in + 1;

  // store output in pipeline register
  always @(posedge clk) begin
    reg_out <= out;
  end

endmodule
module Stage1 #(
  parameter n = 4
) (
  input [n-1:0] in,
  output [n-1:0] out,
  input clk
);

  reg [n-1:0] reg_out; // pipeline register

  // perform computation in this stage
  assign out = in + 2;

  // store output in pipeline register
  always @(posedge clk) begin
    reg_out <= out;
  end

endmodule
module Stage2 #(
  parameter n = 4
) (
  input [n-1:0] in,
  output [n-1:0] out,
  input clk
);

  reg [n-1:0] reg_out; // pipeline register

  // perform computation in this stage
  assign out = in + 3;

  // store output in pipeline register
  always @(posedge clk) begin
    reg_out <= out;
  end

endmodule