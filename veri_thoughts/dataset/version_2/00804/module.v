module First_Phase_M_W32 (clk, rst, load, Data_MX, Data_MY, Op_MX, Op_MY);
  input [31:0] Data_MX;
  input [31:0] Data_MY;
  output [31:0] Op_MX;
  output [31:0] Op_MY;
  input clk, rst, load;
  wire n1;

  RegisterMult_W32 XMRegister (.clk(clk), .rst(rst), .load(n1), .D(Data_MX), .Q(Op_MX));
  RegisterMult_W32 YMRegister (.clk(clk), .rst(rst), .load(n1), .D(Data_MY), .Q(Op_MY));
  CLKBUFX2TS U1 (.A(load), .Y(n1));
endmodule

module RegisterMult_W32 (clk, rst, load, D, Q);
  input clk, rst, load;
  input [31:0] D;
  output reg [31:0] Q;
  
  always @(posedge clk) begin
    if (rst) begin
      Q <= 32'h0;
    end else if (load) begin
      Q <= D;
    end
  end
endmodule

module CLKBUFX2TS (A, Y);
  input A;
  output Y;
  
  assign Y = A;
endmodule