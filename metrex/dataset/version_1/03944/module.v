module mux(input ctrl, input [0:0] D0, input [0:0] D1, output [0:0] S);
  wire [0:0] D0_wire;
  wire [0:0] D1_wire;
  wire [0:0] S_wire;
  wire ctrl_wire;

  assign D0_wire[0] = D0[0];
  assign D1_wire[0] = D1[0];

  assign S[0] = S_wire[0];

  assign ctrl_wire = ctrl;

  assign S_wire[0] = (ctrl_wire) ? D1_wire[0] : D0_wire[0];
endmodule