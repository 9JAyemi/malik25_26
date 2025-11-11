module mux_2to1 (
    input A,
    input B,
    input Sel,
    output Y
);

    wire and_out, or_out;

    // Implement the AND gate
    and_gate and_gate_inst (
        .A(A),
        .B(Sel),
        .Z(and_out)
    );

    // Implement the OR gate
    or_gate or_gate_inst (
        .A(B),
        .B(and_out),
        .Z(or_out)
    );

    // Assign the output
    assign Y = or_out;

endmodule

module and_gate (
    input A,
    input B,
    output Z
);

    assign Z = A & B;

endmodule

module or_gate (
    input A,
    input B,
    output Z
);

    assign Z = A | B;

endmodule