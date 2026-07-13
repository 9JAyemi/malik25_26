
module xor_gate(input a, b, control, output out);
  wire xor_result;
  assign xor_result = a ^ b;

  assign out = control ? xor_result : 0;
endmodule