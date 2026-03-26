
module lookahead(a, b, c_in, sum, c_out);
    input a, b, c_in;
    output sum, c_out;
    wire g, p;

    // Calculate generate and propagate signals
    assign g = a & b;
    assign p = ~a & ~b;

    // Calculate sum and carry-out signals
    assign sum = p ^ (c_in ^ g);
    assign c_out = (g | (p & c_in));
endmodule

module test_lookahead(a, b, c_in, sum, c_out);
    input a, b, c_in;
    output sum, c_out;
    lookahead la(a, b, c_in, sum, c_out);
endmodule
