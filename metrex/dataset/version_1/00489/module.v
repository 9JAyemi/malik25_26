module four_input_and_gate (
    output X,
    input A1,
    input A2,
    input B1,
    input C1
);

    wire W1, W2, W3;

    and and1 (
        W1,
        A1,
        A2
    );

    and and2 (
        W2,
        W1,
        W1
    );

    and and3 (
        W3,
        W2,
        W2
    );

    assign X = W3;

endmodule