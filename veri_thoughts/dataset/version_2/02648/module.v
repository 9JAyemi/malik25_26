module and_gate(input a, b, c, output out);
  wire and_output;
  
  and3_gate and3_inst(.a(a), .b(b), .c(c), .out(and_output));
  or2_gate or2_inst(.a(and_output), .b(c), .out(out));
  
endmodule

module and3_gate(input a, b, c, output out);
  assign out = a & b & c;
endmodule

module or2_gate(input a, b, output out);
  assign out = a | b;
endmodule