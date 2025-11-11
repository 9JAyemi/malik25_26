
module D_FlipFlop (
  output reg Q,
  input D,
  input CLK,
  input RST
);

  always @(posedge CLK or posedge RST) begin
    if (RST) begin
      Q <= 1'b0;
    end else begin
      Q <= D;
    end
  end

endmodule
module full_adder (
  output S,
  output C_out,
  input A,
  input B,
  input C_in
);

  wire w1;
  wire w2;

  assign w1 = A ^ B;
  assign w2 = A & B;

  wire [0:0] CLK = 1'b0;
  wire [0:0] RST = 1'b0;
  wire [0:0] Q;

  D_FlipFlop dffp1(
    .Q(C_out),
    .D(w2),
    .CLK(CLK),
    .RST(RST)
  );

  assign S = w1 ^ C_in;
endmodule
module ripple_adder (
  output [3:0] Sum,
  output Cout,
  input [3:0] A,
  input [3:0] B,
  input Cin
);

  wire [3:0] s;
  wire [3:0] c;

  full_adder fa0(
    .S(s[0]),
    .C_out(c[0]),
    .A(A[0]),
    .B(B[0]),
    .C_in(Cin)
  );

  full_adder fa1(
    .S(s[1]),
    .C_out(c[1]),
    .A(A[1]),
    .B(B[1]),
    .C_in(c[0])
  );

  full_adder fa2(
    .S(s[2]),
    .C_out(c[2]),
    .A(A[2]),
    .B(B[2]),
    .C_in(c[1])
  );

  full_adder fa3(
    .S(s[3]),
    .C_out(Cout),
    .A(A[3]),
    .B(B[3]),
    .C_in(c[2])
  );

  assign Sum = s;
endmodule