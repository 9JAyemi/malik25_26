
module shift_and(input clk, input a, b, output out);
  // Clock input for shifting the stored inputs through the shift register
  // Two binary inputs a and b to be stored in the shift register
  // Binary output out generated from the logical AND of the stored inputs.
  
  // 3-bit shift register module from problem 1
  reg [2:0] shift_reg;
  always @(posedge clk) begin
    shift_reg[2] <= shift_reg[1];
    shift_reg[1] <= shift_reg[0];
    shift_reg[0] <= a;
  end
  
  // Instantiate AND gate module from problem 2
  and_gate and1(shift_reg[2], b, out);
  
  // Output generated from the logical AND of the stored inputs

endmodule
module and_gate(a, b, out);
  input a, b;
  output out;

  assign out = a & b;
endmodule