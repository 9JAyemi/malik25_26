module and_gate(input a, b, output out);
  wire nand_out;
  nand_gate nand_inst(a, b, nand_out);
  inverter inv_inst(nand_out, out);
endmodule

module nand_gate(input a, b, output out);
  assign out = ~(a & b);
endmodule

module inverter(input in, output out);
  assign out = ~in;
endmodule