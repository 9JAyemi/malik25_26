
module ECC #(
  parameter n = 8, // number of bits for the coordinates
  parameter p = 256, // prime number that defines the finite field
  parameter a = 1, // coefficient a of the elliptic curve
  parameter b = 2 // coefficient b of the elliptic curve
)(
  input [p-1:0] P,
  input [n-1:0] A,
  input [n-1:0] B,
  input [n-1:0] Px,
  input [n-1:0] Py,
  input [n-1:0] Qx,
  input [n-1:0] Qy,
  output [n-1:0] Rx,
  output [n-1:0] Ry,
  output [n-1:0] Sx,
  output [n-1:0] Sy
);

// coordinates of point P on the elliptic curve
parameter P_x = 8'b00000001;
parameter P_y = 8'b00000010;

// coordinates of point Q on the elliptic curve
parameter Q_x = 8'b00000011;
parameter Q_y = 8'b00000001;

// calculate point R = P + Q
wire [n-1:0] x1 = P_x;
wire [n-1:0] y1 = P_y;
wire [n-1:0] x2 = Q_x;
wire [n-1:0] y2 = Q_y;

wire [n-1:0] x3;
wire [n-1:0] y3;

wire [n-1:0] m;
wire [n-1:0] m2;
wire [n-1:0] x1x2;
wire [n-1:0] x3x1;
wire [n-1:0] y3y1;

assign x1x2 = x1 + x2;
assign m = (y2 - y1) * (x2 - x1x2)^(p-2);
assign m2 = m^2;
assign x3 = m2 - x1x2 - a;
assign x3x1 = x3 - x1;
assign y3 = m * x1x2 - m * x3 - y1;
assign y3y1 = y3 - y1;

assign Rx = x3;
assign Ry = y3;

// calculate point S = P - Q
wire [n-1:0] Qy_neg = ~Qy + 1;
wire [n-1:0] Qx_neg = Qx;
wire [n-1:0] Sx;
wire [n-1:0] Sy;

assign Sy = y1 + Qy_neg;
assign Sx = x1 + Qx_neg;

endmodule