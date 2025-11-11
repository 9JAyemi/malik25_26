
module base (
    output X,
    input A1,
    input A2,
    input B1,
    input B2
);

    assign X = (A1 ^ A2) & (B1 ^ B2);

endmodule
module wrapper_module (
    output X,
    input A1,
    input A2,
    input B1,
    input B2
);

    // Instantiate the correct module
    base instance_name (
        .X(X),
        .A1(A1),
        .A2(A2),
        .B1(B1),
        .B2(B2)
    );

endmodule