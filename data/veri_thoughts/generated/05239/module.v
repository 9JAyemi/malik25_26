module complement_buffer (
    Y,
    A
);

    // Module ports
    output Y;
    input  A;

    // Local signals
    wire not0_out_Y;

    // Combinational logic circuit
    assign not0_out_Y = ~A;
    assign Y = not0_out_Y;

endmodule