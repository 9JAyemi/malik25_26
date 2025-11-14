
module a221o_2 (
    input X,
    input A1,
    input A2,
    input B1,
    input B2,
    input C1,
    output Y
);

    assign Y = (A1 & B1 & C1) | (A2 & B2 & C1);

endmodule
