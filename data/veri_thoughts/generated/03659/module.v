module magnitude_comparator (
    input [3:0] a,
    input [3:0] b,
    output eq,
    output gt
);

    assign eq = (a == b);
    assign gt = (a > b);

endmodule