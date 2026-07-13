module and_gate (
    output Y,
    input A1,
    input A2,
    input B1_N,
    input B2_N
);

    assign Y = ~(A1 & A2 & B1_N & B2_N);

endmodule

