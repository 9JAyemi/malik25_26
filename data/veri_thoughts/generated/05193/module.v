module mux2to1_txg(
    input A,
    input B,
    input SEL,
    output Y
);

    wire SEL_B;
    tx_gate tx1(.A(A), .B(SEL_B), .Y(Y));
    tx_gate tx2(.A(B), .B(SEL), .Y(SEL_B));

endmodule

module tx_gate(
    input A,
    input B,
    output Y
);

    assign Y = A & B;

endmodule