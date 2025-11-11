
module mux_4to1_and(input [3:0] a, b, c, d, input [1:0] sel, output [3:0] y);
  wire [3:0] mux1_out, mux2_out;

  // First 2-to-1 MUX
  mux2to1 mux1(.a(a), .b(b), .sel(sel[0]), .y(mux1_out));
  
  // Second 2-to-1 MUX
  mux2to1 mux2(.a(c), .b(d), .sel(sel[0]), .y(mux2_out));
  
  // Final 2-to-1 MUX
  mux2to1 mux3(.a(mux1_out), .b(mux2_out), .sel(sel[1]), .y(y));
  
  // Bitwise AND gate
  // assign y = y & 4'b1010;
endmodule
module mux2to1(input [3:0] a, b, input sel, output [3:0] y);
  assign y = sel ? b : a;
endmodule