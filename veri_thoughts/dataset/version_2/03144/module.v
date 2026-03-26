module and_or_buf (
    input [2:0] A,
    input B,
    output X
);

    wire or_out;
    wire and_out;

    // Perform OR operation on first three bits of A
    or or_inst (
        .out(or_out),
        .in1(A[2]),
        .in2(A[1]),
        .in3(A[0])
    );

    // Perform AND operation on output of previous step and B
    and and_inst (
        .out(and_out),
        .in1(or_out),
        .in2(B)
    );

    // Assign output of previous step to X
    assign X = and_out;

endmodule