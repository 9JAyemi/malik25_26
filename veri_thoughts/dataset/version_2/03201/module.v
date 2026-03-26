
module nor_gate (
    input A,
    input B,
    output Y
);

    wire w1, w2, w3;
    nor (
        w1,
        A,
        A,
        B,
        B
    );
    nor (
        w2,
        w1,
        w1,
        w1,
        w1
    );
    nor (
        w3,
        w2,
        w2,
        w2,
        w2
    );
    assign Y = w3;

endmodule
