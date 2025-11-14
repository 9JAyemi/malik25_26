
module add16(
    input [15:0] a,   // First 16-bit input
    input [15:0] b,   // Second 16-bit input
    output [15:0] sum // 16-bit output sum
);

    assign sum = a + b;   // Add the two inputs and assign the result to the output

endmodule
module top_module(
    input [31:0] a,       // First 32-bit input
    input [31:0] b,       // Second 32-bit input
    input [1:0] select,   // Select input to choose between inputs
    input clk,            // Clock input
    output [31:0] sum     // 32-bit output sum
);

    wire [15:0] adder1_out, adder2_out;  // Intermediate outputs of the 16-bit adders
    wire [31:0] mux_out;                                        // Output of the 2:1 multiplexer

    // Instantiate two 16-bit adders
    add16 adder1(.a(a[15:0]), .b(b[15:0]), .sum(adder1_out));
    add16 adder2(.a(a[31:16]), .b(b[31:16]), .sum(adder2_out));

    // Implement the 2:1 multiplexer using combinational logic
    assign mux_out = (select == 2'b0) ? a[31:0] : b[31:0];

    // Combine the outputs of the adders and the multiplexer to get the final output
    assign sum = {adder2_out, adder1_out} + mux_out;

endmodule