module three_input_module (
    input input_a,
    input input_b,
    input input_c,
    output output_y
);

    wire a_and_b = input_a & input_b;
    wire a_and_c = input_a & input_c;
    wire b_and_c = input_b & input_c;
    wire a_or_b_or_c = input_a | input_b | input_c;

    assign output_y = (a_or_b_or_c && !b_and_c) || (input_a && !a_and_b && !a_and_c) || (input_b && !a_and_b && !b_and_c) || (input_c && !a_and_c && !b_and_c);

endmodule