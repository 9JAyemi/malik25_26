module DEMUX (
  input in,
  output out0,
  output out1,
  output out2,
  output out3
);

  wire d0, d1, d2, d3;
  wire a0, a1, a2, a3;

  // 2-to-4 decoder
  decoder_2to4 decoder (
    .in(in),
    .out0(d0),
    .out1(d1),
    .out2(d2),
    .out3(d3)
  );

  // AND gates
  assign a0 = d0 & ~d1 & ~d2 & ~d3;
  assign a1 = ~d0 & d1 & ~d2 & ~d3;
  assign a2 = ~d0 & ~d1 & d2 & ~d3;
  assign a3 = ~d0 & ~d1 & ~d2 & d3;

  // Output signals
  assign out0 = a0;
  assign out1 = a1;
  assign out2 = a2;
  assign out3 = a3;

endmodule

// 2-to-4 decoder module
module decoder_2to4 (
  input in,
  output out0,
  output out1,
  output out2,
  output out3
);

  assign out0 = ~in & ~in;
  assign out1 = ~in & in;
  assign out2 = in & ~in;
  assign out3 = in & in;

endmodule