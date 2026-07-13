
module and_gate_with_inverter (
    output Y,
    input  A1,
    input  A2,
    input  A3,
    input  B1,
    input  C1
);

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;

    wire B1_inv;
    assign B1_inv = ~B1;

    wire and_gate_output;
    and (and_gate_output, A1, A2, A3);

    assign Y = (C1 == 1'b1) ? 1'b0 : (and_gate_output & B1_inv);

endmodule
