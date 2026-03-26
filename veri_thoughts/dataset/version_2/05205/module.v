module system_vga_hessian_0_0_bindec_0 (
  output [2:0] enb_array,
  input enb,
  input [1:0] addrb
);

  wire [1:0] addrb_wire;
  wire enb_wire;
  wire [2:0] enb_array_wire;

  assign addrb_wire = addrb;
  assign enb_wire = enb;
  assign enb_array_wire = enb_array;

  assign enb_array[0] = ((addrb_wire[1] & ~addrb_wire[0]) | enb_wire);
  assign enb_array[1] = ((addrb_wire[0] & ~addrb_wire[1]) | enb_wire);
  assign enb_array[2] = ((enb_wire & ~addrb_wire[0]) | addrb_wire[1]);

endmodule