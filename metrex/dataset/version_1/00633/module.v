
module four_input_or (
    input A,
    input B,
    input C,
    input D,
    output X
);

    wire or1_out;

    or (or1_out, A, B, C, D);

    assign X = or1_out;

endmodule
