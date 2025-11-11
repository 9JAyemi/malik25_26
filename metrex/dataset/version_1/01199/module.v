
module v468a05 (
  input [31:0] ve841af,
  output [7:0] vdd0469,
  output [7:0] v4ba85d,
  output [7:0] vf93ecb,
  output [7:0] vc6471a
);

  // Instantiate v468a05_v9a2a06 module
  v468a05_v9a2a06 v9a2a06 (
    .i(ve841af),
    .o0(vdd0469),
    .o1(vf93ecb),
    .o2(v4ba85d),
    .o3(vc6471a)
  );

endmodule
module v468a05_v9a2a06 (
  input [31:0] i,
  output [7:0] o0,
  output [7:0] o1,
  output [7:0] o2,
  output [7:0] o3
);

  wire [31:0] w0;
  wire [31:0] w1;
  wire [31:0] w2;
  wire [31:0] w3;
  wire [31:0] w4;

  // Assign input to wire
  assign w0 = i;

  // Xors of i
  assign w1 = i ^ 32'h09436c12;
  assign w2 = i ^ 32'h1423bf56;
  assign w3 = i ^ 32'h22fb9439;
  assign w4 = i ^ 32'h30648dbc;

  // Assign wires to outputs
  assign o0 = w1[7:0];
  assign o1 = w2[7:0];
  assign o2 = w3[7:0];
  assign o3 = w4[7:0];

endmodule