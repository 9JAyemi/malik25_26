
module and_gate (
    output Y,
    input A,
    input B
);

    wire wire1;

    and (
        wire1, // Use . operator to specify ports
        A,
        B
    );

    assign Y = wire1; // Assign the output to the wire

endmodule