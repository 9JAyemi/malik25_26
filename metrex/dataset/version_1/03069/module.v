
module comb_logic (
    output Y,
    input  A,
    input  B,
    input  C
);

    // Output
    wire Y;

    // Inputs
    wire A;
    wire B;
    wire C;

    // Internal wires
    wire not_C;
    wire and_AB;

    // Instantiate NOT gate for C
    not (not_C, C);

    // Instantiate AND gate for A and B
    and (and_AB, A, B);

    // Instantiate OR gate for and_AB and not_C
    or (Y, and_AB, not_C);

endmodule
