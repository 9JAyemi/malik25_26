
module gen_test3(a, b, sel, y, z);

input [3:0] a, b;
input sel;
output [3:0] y, z;

assign y[1:0] = sel ? a[1:0] : b[1:0]; // Fix the part select indices
assign z[1:0] = sel ? b[1:0] : a[1:0]; // Fix the part select indices
assign y[2] = sel ? a[2] : b[2];
assign z[2] = sel ? b[2] : a[2];
assign y[3] = sel ? a[3] : b[3];
assign z[3] = sel ? b[3] : a[3];

endmodule
