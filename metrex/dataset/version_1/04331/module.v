module and4(
    input A,
    input B,
    input C,
    input D,
    output X
);

    wire w1, w2, w3;

    and and1(
        w1,
        A,
        B
    );

    and and2(
        w2,
        w1,
        1'b1
    );

    and and3(
        w3,
        w2,
        1'b1
    );

    and and4(
        X,
        w3,
        1'b1
    );

endmodule