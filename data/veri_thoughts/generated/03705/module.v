
module mux_2to1(input i0, i1, s, output z);
  assign z = s ? i1 : i0;
endmodule

module mux32bit_2to1(input [31:0] i0, i1,
                      input s,
                      output [31:0] z);
  wire [31:0] mux_outs;
  assign mux_outs = s ? i1 : i0;
  assign z = mux_outs;
endmodule
