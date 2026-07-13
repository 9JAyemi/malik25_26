
module top_module(
  input clk, // Clock input
  input reset, // Synchronous active-high reset
  input [7:0] in, // 8-bit input for the shift register
  output out // Output of the NOR gate module
);

  wire [2:0] shift_out;
  wire nand_out1, nand_out2;

  shift_register sr(
    .clk(clk),
    .in(in[0]),
    .reset(reset), // Added reset to the shift register module
    .out(shift_out)
  );

  nand_gate n1(
    .a(shift_out[0]),
    .b(shift_out[1]),
    .out(nand_out1)
  );

  nand_gate n2(
    .a(nand_out1),
    .b(shift_out[2]),
    .out(nand_out2)
  );

  nor_gate ng(
    .a(nand_out2),
    .b(nand_out2),
    .out(out)
  );

endmodule

module shift_register(
  input clk,
  input [0:0] in, // Input to the shift register
  input reset, // Active-high reset for the shift register
  output reg [2:0] out // 3-bit output of the shift register
);

  always @(posedge clk) begin
    if (reset) begin
      out <= 3'b0; // Reset the shift register to all zeros
    end else begin
      out <= {out[1:0], in}; // Shift the input into the shift register
    end
  end

endmodule

module nand_gate(
  input a, b, // Input signals to the NAND gate
  output out // Output signal of the NAND gate
);

  assign out = ~(a & b);

endmodule

module nor_gate(
  input a, b, // Input signals to the NOR gate
  output out // Output signal of the NOR gate
);

  assign out = ~(a | b);

endmodule
