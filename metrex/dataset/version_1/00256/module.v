
module bitwise_operators #(
    parameter n = 8 // length of binary numbers
)(
    input [n-1:0] num1,
    input [n-1:0] num2,
    output reg [n-1:0] result
);

// Bitwise AND, OR, XOR, and NOT operations
always @* begin
    result = num1 & num2; // AND
    result = num1 | num2; // OR
    result = num1 ^ num2; // XOR
    result = ~num1; // NOT
end

endmodule