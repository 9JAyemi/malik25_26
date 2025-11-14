
module restoring_division_16bit (
    input signed [15:0] dividend,
    input signed [15:0] divisor,
    output reg signed [15:0] quotient,
    output reg signed [15:0] remainder
);

reg signed [15:0] remainder_reg;
reg signed [15:0] divisor_reg;
reg signed [15:0] quotient_reg;
reg signed [15:0] dividend_reg;
reg [4:0] count;

always @(*) begin
    count = 0;
    remainder_reg = dividend;
    divisor_reg = divisor;
    quotient_reg = 0;
    dividend_reg = dividend;

    if (dividend[15] == 1) begin
        remainder_reg = -dividend;
        dividend_reg = -dividend;
    end

    if (divisor[15] == 1) begin
        divisor_reg = -divisor;
    end

    for (count = 0; count < 16; count = count + 1) begin
        remainder_reg = remainder_reg << 1;
        quotient_reg = quotient_reg << 1;
        remainder_reg[0] = dividend_reg[15];
        dividend_reg = dividend_reg << 1;

        remainder_reg = remainder_reg - divisor_reg;

        if (remainder_reg[15] == 1) begin
            remainder_reg = remainder_reg + divisor_reg;
        end else begin
            quotient_reg[0] = 1;
        end

        count = count + 1;
    end

    if (dividend[15] == 1 && divisor[15] == 1) begin
        quotient = quotient_reg;
        remainder = -remainder_reg;
    end else if (dividend[15] == 1 || divisor[15] == 1) begin
        quotient = -quotient_reg;
        remainder = remainder_reg;
    end else begin
        quotient = quotient_reg;
        remainder = remainder_reg;
    end
end

endmodule