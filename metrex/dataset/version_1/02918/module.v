
module sky130_fd_sc_ms__or4b_1 (
    input A,
    input B,
    input C,
    input D,
    output X
);

    assign X = A | B | C | D;

endmodule

module or4 (
    input A,
    input B,
    input C,
    input D,
    output X
);

    wire [3:0] or_inputs;
    assign or_inputs = {A, B, C, ~D};

    sky130_fd_sc_ms__or4b_1 or_gate (
        .X(X),
        .A(or_inputs[0]),
        .B(or_inputs[1]),
        .C(or_inputs[2]),
        .D(or_inputs[3])
    );

endmodule
