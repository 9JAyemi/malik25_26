
module mux_4to1(
  input [3:0] a, b, c, d,
  input [1:0] sel,
  output reg [3:0] y
);

  wire [3:0] ab_sel, cd_sel;

  // First level of 2-to-1 MUXes
  mux2to1 mux_ab(.a(a[0]), .b(b[0]), .sel(sel[0]), .y(ab_sel[0]));
  mux2to1 mux_cd(.a(c[0]), .b(d[0]), .sel(sel[0]), .y(cd_sel[0]));
  mux2to1 mux_ab1(.a(a[1]), .b(b[1]), .sel(sel[0]), .y(ab_sel[1]));
  mux2to1 mux_cd1(.a(c[1]), .b(d[1]), .sel(sel[0]), .y(cd_sel[1]));
  mux2to1 mux_ab2(.a(a[2]), .b(b[2]), .sel(sel[0]), .y(ab_sel[2]));
  mux2to1 mux_cd2(.a(c[2]), .b(d[2]), .sel(sel[0]), .y(cd_sel[2]));
  mux2to1 mux_ab3(.a(a[3]), .b(b[3]), .sel(sel[0]), .y(ab_sel[3]));
  mux2to1 mux_cd3(.a(c[3]), .b(d[3]), .sel(sel[0]), .y(cd_sel[3]));

  // Second level of 2-to-1 MUX to select between the outputs of the first level
  always @(*) begin
    case (sel[1])
      1'b0: y = ab_sel;
      1'b1: y = cd_sel;
    endcase
  end

endmodule
module mux2to1(
  input a, b, sel,
  output reg y
);

  always @(*) begin
    y = (sel == 1'b0) ? a : b;
  end

endmodule