module nor_gate(
    input A,
    input B,
    output Y
);

    wire notA, notB;
    nor2 u1(.A(A), .B(A), .Y(notA));
    nor2 u2(.A(B), .B(B), .Y(notB));
    nor2 u3(.A(notA), .B(notB), .Y(Y));

endmodule

module nor2 (input A, input B, output Y);

    assign Y = ~(A | B);
endmodule