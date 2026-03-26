
module nor2_gate (
    input     wire        A,
    input     wire        B,
    input     wire        VPWR,
    input     wire        VGND,
    output    wire        Y
);

    // Implement NOR2 gate logic
    assign Y = ~(A | B);

endmodule
