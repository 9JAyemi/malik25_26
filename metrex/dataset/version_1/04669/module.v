module multiplier(
    input wire clk,       // System clock
    input wire rst,       // Reset input
    input wire [15:0] in1, // First 16-bit input
    input wire [15:0] in2, // Second 16-bit input
    output reg [31:0] out  // 32-bit output
);

reg [15:0] shift_reg; // Register to hold shifted input
reg [31:0] sum_reg;   // Register to hold accumulated output

always @(posedge clk) begin
    if (rst) begin
        shift_reg <= 0;
        sum_reg <= 0;
    end else begin
        // Shift input by one bit and select shifted or original input based on current bit of in1
        shift_reg <= {shift_reg[14:0], in2[0]};
        out <= sum_reg + (in1[0] ? shift_reg : in2);
        sum_reg <= out;
    end
end

endmodule

module top_module( 
    input wire clk,       // System clock
    input wire [15:0] in1, // First 16-bit input
    input wire [15:0] in2, // Second 16-bit input
    output wire [31:0] out  // 32-bit output
);

wire [31:0] mult_out;
multiplier mult(clk, 1'b0, in1, in2, mult_out); // Instantiate multiplier module

// Functional module to add the two inputs
assign out = in1 + in2 + mult_out;

endmodule