module multiplier_32bit (
  input [15:0] a_1,
  input [15:0] b_1,
  input [15:0] a_2,
  input [15:0] b_2,
  input select,
  output reg [31:0] result
);

  wire [31:0] mul_result_1;
  wire [31:0] mul_result_2;

  // Multiplication module 1
  mult_1 mult_1_inst (
    .a(a_1),
    .b(b_1),
    .result(mul_result_1)
  );

  // Multiplication module 2
  mult_2 mult_2_inst (
    .a(a_2),
    .b(b_2),
    .result(mul_result_2)
  );

  // Control module
  always @ (select) begin
    if (select == 1'b0) begin
      result <= mul_result_1;
    end else begin
      result <= mul_result_2;
    end
  end

endmodule

// 16-bit multiplication module
module mult_1 (
  input [15:0] a,
  input [15:0] b,
  output reg [31:0] result
);

  always @ (a, b) begin
    result <= a * b;
  end

endmodule

// 16-bit multiplication module
module mult_2 (
  input [15:0] a,
  input [15:0] b,
  output reg [31:0] result
);

  always @ (a, b) begin
    result <= a * b;
  end

endmodule