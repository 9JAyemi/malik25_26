module ripple_adder_mux (
  input [3:0] A,
  input [3:0] B,
  input cin,
  input select,
  output [3:0] out
);

  // Ripple Carry Adder
  wire [3:0] sum;
  wire cout;
  assign {cout, sum} = A + B + cin;

  // 2:1 Multiplexer
  wire [3:0] constant_value = 4'b1111; // Example constant value
  assign out = select ? sum : constant_value;

endmodule

module top_module (
  input [3:0] A,
  input [3:0] B,
  input cin,
  input select,
  output [3:0] out
);

  ripple_adder_mux adder_mux(
    .A(A),
    .B(B),
    .cin(cin),
    .select(select),
    .out(out)
  );

endmodule