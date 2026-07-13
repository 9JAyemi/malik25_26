
module AND4(out1, in1, in2, in3, in4);

  parameter gate_delay = 1; // Define gate delay parameter

  input in1, in2, in3, in4;
  output out1;

  wire and1, and2;

  and #(gate_delay) and1 (and2, in1, in2);
  and #(gate_delay) and2 (out1, and2, in3, in4);

endmodule