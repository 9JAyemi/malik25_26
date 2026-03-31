```systemverilog
module ripple_carry_adder_sva (
  input logic CLK,
  input logic [3:0] A,
  input logic [3:0] B,
  input logic Cin,
  output logic [3:0] Sum,
  output logic Cout
);

  // Combinational logic: SUM and Cout are determined by A, B, and Cin
  // Clocked assertions to ensure the combinational logic is correct
  // at the rising edge of the clock

  // SUM is the XOR of A, B, and Cin
  sum_correct: assert property (
    @(posedge CLK) disable iff (!CLK) Sum == (A ^ B ^ Cin)
  );

  // Cout is the OR of the ANDs of A and B, A and Cin, and B and Cin
  cout_correct: assert property (
    @(posedge CLK) disable iff (!CLK) Cout == ((A & B) | (A & Cin) | (B & Cin))
  );

endmodule
```