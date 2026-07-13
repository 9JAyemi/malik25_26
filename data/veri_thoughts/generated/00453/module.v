
module test(
    input a1,
    input s1,
    input s2,
    input s3,
    output i1,
    output i2,
    output i3,
    output i4,
    output i5,
    output i6,
    output i7,
    output i8
);

// Logic to generate the outputs based on the inputs
assign i1 = a1 & s1;
assign i2 = a1 & s2;
assign i3 = a1 & s3;
assign i4 = ~a1 & s1;
assign i5 = ~a1 & s2;
assign i6 = ~a1 & s3;
assign i7 = s1 & s2 & s3;
assign i8 = ~a1 & ~s1 & ~s2 & ~s3;

endmodule
