module or4 (
    output X,
    input A,
    input B,
    input C,
    input D
);

    wire [3:0] or_input;
    assign or_input = {A, B, C, D};
    
    or base (
        X,
        or_input[0],
        or_input[1],
        or_input[2],
        or_input[3]
    );

endmodule