module my_or3 (
    input A,
    input B,
    input C_N,
    output X,
);

    assign X = A | B | C_N;

endmodule