
module nor_and_gate (
    input A, B, C, D,
    output Y
);

    // Local signals
    wire nor_out, and_out;

    // NOR gate
    nor (nor_out, A, B);

    // AND gate
    and (and_out, nor_out, C, D);

    // Output buffer
    buf (Y, and_out);

endmodule