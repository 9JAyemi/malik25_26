
module and_gate (
    input A, B,
    output Y
);

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;

    and (Y, A, B); // gate output

endmodule
