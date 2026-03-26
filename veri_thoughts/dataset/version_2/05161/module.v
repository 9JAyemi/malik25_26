
module four_input_module (
    X,
    A1,
    A2,
    B1,
    B2
);

    output X;
    input A1;
    input A2;
    input B1;
    input B2;

    nand (
        X,
        A1,
        B1
    );

endmodule