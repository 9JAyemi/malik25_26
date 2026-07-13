module four_input_one_output (
    input a,
    input b,
    input c,
    input d,
    output x
);

    wire a_and_not_b;
    wire not_a_and_not_b_and_not_c;
    wire not_a_and_not_b_and_c_and_d;

    assign a_and_not_b = a & ~b;
    assign not_a_and_not_b_and_not_c = ~a & ~b & ~c;
    assign not_a_and_not_b_and_c_and_d = ~a & ~b & c & d;

    assign x = a | a_and_not_b | not_a_and_not_b_and_not_c | not_a_and_not_b_and_c_and_d;

endmodule