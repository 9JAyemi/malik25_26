module MUX2 (a, b, sel, out);
  input a, b, sel;
  output out;

  assign out = sel ? b : a;
endmodule

module MUX4 (a0, a1, b0, b1, sel0, sel1, out);
  input a0, a1, b0, b1, sel0, sel1;
  output out;

  wire temp0, temp1;

  MUX2 i0 (.a(a0), .b(a1), .sel(sel0), .out(temp0));
  MUX2 i1 (.a(b0), .b(b1), .sel(sel0), .out(temp1));
  MUX2 i2 (.a(temp0), .b(temp1), .sel(sel1), .out(out));
endmodule