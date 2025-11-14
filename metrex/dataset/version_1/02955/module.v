module xor_splitter (
  input wire [15:0] in,
  input wire a,
  input wire b,
  output wire [7:0] out_xor
);

  wire [7:0] upper_byte;
  wire [7:0] lower_byte;

  // instantiate the half-word splitter module
  splitter16 splitter_inst (
    .in(in),
    .a(a),
    .b(b),
    .upper(upper_byte),
    .lower(lower_byte)
  );

  // instantiate the XOR gate module
  xor_gate xor_inst (
    .in1(upper_byte),
    .in2(lower_byte),
    .out(out_xor)
  );

endmodule

module splitter16 (
  input wire [15:0] in,
  input wire a,
  input wire b,
  output wire [7:0] upper,
  output wire [7:0] lower
);

  assign upper = (a == 1'b0) ? in[7:0] : in[15:8];
  assign lower = (b == 1'b0) ? in[7:0] : in[15:8];

endmodule

module xor_gate (
  input wire [7:0] in1,
  input wire [7:0] in2,
  output wire [7:0] out
);

  assign out = in1 ^ in2;

endmodule