
module shift_register #(
    parameter N = 4 // Default value for N is 4
) (
    input clk,
    input reset, // Synchronous active-high reset
    input [N-1:0] D, // Input data for the shift register
    input L, // Load input for the shift register
    output reg [N-1:0] Q // Output data from the shift register
);


always @(posedge clk) begin
    if (reset) begin
        Q <= 0;
    end else if (L) begin
        Q <= D;
    end else begin
        Q <= {Q[N-2:0], Q[N-1]};
    end
end

endmodule

module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [3:0] D0, // Input data for the 4-bit shift register
    input [15:0] D1, // Input data for the 16-bit shift register
    input select, // Select input to choose between shift registers
    input L, // Load input for the selected shift register
    output [19:0] out // Output of the bitwise OR operation
);

wire [3:0] Q0;
wire [15:0] Q1;

shift_register #(.N(4)) sr0 (
    .clk(clk),
    .reset(reset),
    .D(D0),
    .L(L & ~select),
    .Q(Q0)
);

shift_register #(.N(16)) sr1 (
    .clk(clk),
    .reset(reset),
    .D(D1),
    .L(L & select),
    .Q(Q1)
);

assign out = Q1 | Q0 | 20'h0; // Fix the issue by using the bitwise OR operator instead of the concatenation operator

endmodule
