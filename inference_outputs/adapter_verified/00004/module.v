module mux_2to1(
    input a,
    input b,
    input sel,
    output y
);

    wire not_sel;
    wire a_and_sel;
    wire b_and_not_sel;

    // Invert the select signal
    assign not_sel = ~sel;

    // AND gate between a and select signal
    assign a_and_sel = a & not_sel;

    // AND gate between b and inverted select signal
    assign b_and_not_sel = b & sel;

    // OR gate between the two AND gates
    assign y = a_and_sel | b_and_not_sel;

endmodule