
module calculator (
    input [7:0] op1,
    input [7:0] op2,
    output [7:0] result,
    output carry,
    output overflow,
    output error
);

    wire [8:0] sum;
    wire [8:0] diff;
    wire [15:0] prod;
    wire [7:0] quotient;
    wire [7:0] remainder;
    
    assign sum = op1 + op2;
    assign diff = op1 - op2;
    assign prod = op1 * op2;
    assign overflow = (prod[15:8] != 8'b0) || ((prod[7] == 1) && (op1[7] != op2[7]));
    
    assign quotient = (op2 == 8'b0) ? 8'b0 : op1 / op2;
    assign remainder = (op2 == 8'b0) ? 8'b0 : op1 % op2;
    
    assign carry = (op2 == 8'b0) ? 0 : remainder[7];
    assign error = (op2 == 8'b0);
    assign result = (op2 == 8'b0) ? 8'b0 : quotient;

endmodule