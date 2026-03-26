
module my_and4 (
    input A,
    input B,
    input C,
    input D,
    output X
);

    wire w1, w2, w3;

    assign w1 = A & B;
    assign w2 = w1 & C;
    assign w3 = w2 & D;
    assign X = w3;

endmodule