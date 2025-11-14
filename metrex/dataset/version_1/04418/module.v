module six_signal_module (
    input A1,
    input A2,
    input B1,
    input B2,
    input C1,
    output Y
);

    assign Y = (A1 & A2) | (B1 & B2) | (C1 & (A1 | A2));

endmodule