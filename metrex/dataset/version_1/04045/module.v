module p_aoi222(q, a, b, c, d, e, f);
  output q;
  input a, b, c, d, e, f;
  wire [1:0] internal_0n;
  wire [2:0] int_0n;
  AN2 I0 (q, internal_0n[0], internal_0n[1]);
  IV I1 (internal_0n[1], int_0n[2]);
  NR2 I2 (internal_0n[0], int_0n[0], int_0n[1]);
  AN2 I3 (int_0n[2], e, f);
  AN2 I4 (int_0n[1], c, d);
  AN2 I5 (int_0n[0], a, b);
endmodule

module AN2 (out, in1, in2);
  output out;
  input in1, in2;
  assign out = in1 & in2;
endmodule

module IV (out, in1);
  output out;
  input in1;
  assign out = ~in1;
endmodule

module NR2 (out, in1, in2);
  output out;
  input in1, in2;
  assign out = ~(in1 | in2);
endmodule