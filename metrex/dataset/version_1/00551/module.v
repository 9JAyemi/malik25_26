
module float_mult (
    input [31:0] a,
    input [31:0] b,
    output reg [31:0] product
);

reg [31:0] mantissa_a, mantissa_b, mantissa_product;
reg [7:0] exponent_a, exponent_b, exponent_product;
reg sign_a, sign_b, sign_product;
reg [8:0] guard_bits, round_bit, sticky_bit;

always @(*) begin
    sign_a = a[31];
    sign_b = b[31];
    mantissa_a = {1'b1, a[22:0]};
    mantissa_b = {1'b1, b[22:0]};
    exponent_a = a[30:23];
    exponent_b = b[30:23];
    mantissa_product = mantissa_a * mantissa_b;
    guard_bits = mantissa_product[25:23];
    round_bit = mantissa_product[22];
    sticky_bit = |mantissa_product[21:0];
    exponent_product = exponent_a + exponent_b - 127;
    if (mantissa_product[26]) begin
        mantissa_product = mantissa_product >> 1;
        exponent_product = exponent_product + 1;
    end
    if (guard_bits == 3'b111 || (guard_bits == 3'b110 && (round_bit || sticky_bit))) begin
        mantissa_product = mantissa_product + 1;
        if (mantissa_product[26]) begin
            mantissa_product = mantissa_product >> 1;
            exponent_product = exponent_product + 1;
        end
    end
    sign_product = sign_a ^ sign_b;
    product[31] = sign_product;
    product[30:23] = exponent_product;
    product[22:0] = mantissa_product[22:0];
end
endmodule