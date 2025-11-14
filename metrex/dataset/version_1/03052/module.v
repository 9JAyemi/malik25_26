module LUT3 (
    input I0,
    input I1,
    input I2,
    output O
);

    assign O = ~(I0 & I1 & I2);

endmodule

module mux (
    input ctrl,
    input D0,
    input D1,
    output S
);

    wire [2:0] lut_input;
    wire lut_output;

    assign lut_input[0] = D1;
    assign lut_input[1] = ctrl;
    assign lut_input[2] = D0;

    LUT3 lut (
        .I0(lut_input[0]),
        .I1(lut_input[1]),
        .I2(lut_input[2]),
        .O(lut_output)
    );

    assign S = lut_output;

endmodule