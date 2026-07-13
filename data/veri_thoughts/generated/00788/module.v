
module logic_gates (
  input in1,
  input in2,
  output out
);

// AND gate
wire and_out;
and gate_and(and_out, in1, in2);

// OR gate
wire or_out;
or gate_or(or_out, in1, in2);

// NOT gate
wire not_out;
not gate_not(not_out, in1);

// XOR gate
wire xor_out;
xor gate_xor(xor_out, in1, in2);

// XNOR gate
wire xnor_out;
xnor gate_xnor(xnor_out, in1, in2);

// Output assignment
assign out = and_out; // Replace with the desired output

endmodule