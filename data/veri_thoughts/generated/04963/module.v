
module and4_pg(
    output X,
    input A,
    input B,
    input C,
    input D
);

    wire and0_out, and1_out, and2_out;

    // Instantiate AND gates
    and and0(and0_out, A, B);
    and and1(and1_out, C, D);
    and and2(and2_out, and0_out, and1_out);

    // Instantiate a buffer for output
    buf buf_x(X, and2_out);

endmodule