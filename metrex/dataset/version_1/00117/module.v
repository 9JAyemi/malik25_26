
module xor_gate(input a, b, output out);

  // Structural Verilog module
  wire xored;
  xor m_xor_gate(xored, a, b);
  buf m_buf(out, xored);

endmodule

module m_xor_gate(input a, b, output out);
  assign out = a ^ b;
endmodule
