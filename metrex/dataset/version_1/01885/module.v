
module full_adder(
  input  a,
  input  b,
  input  cin,
  output cout,
  output sum
);

  wire w1, w2, w3;
  assign w1 = a ^ b;
  assign w2 = a & b;
  assign w3 = w1 & cin;
  assign sum = w1 ^ cin;
  assign cout = w2 | w3;

endmodule
module gray_code_counter(
  input        clk,
  input        reset,
  output reg [15:0] Q
);

  always @(posedge clk, negedge reset) begin
    if (reset == 0) begin
      Q <= 16'b0000000000000000;
    end else begin
      Q <= Q ^ ({Q[14:0],1'b0});
    end
  end

endmodule
module top_module(
  input        clk,
  input        reset,
  input        a,
  input        b,
  input        cin,
  output       cout,
  output       sum,
  output [15:0] Q
);

  wire [15:0] gray_code;
  wire adder_sum;
  wire adder_cout;

  gray_code_counter gc(
    .clk(clk),
    .reset(reset),
    .Q(gray_code)
  );

  full_adder fa(
    .a(a),
    .b(b),
    .cin(cin),
    .sum(adder_sum),
    .cout(adder_cout)
  );

  assign sum = adder_sum ^ gray_code[0];
  assign cout = adder_cout;
  assign Q = gray_code;

endmodule