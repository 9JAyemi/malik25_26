
module and_gate_enable(
    output Y,
    input A1,
    input A2,
    input A3,
    input A4,
    input EN
);

    wire inputs;

    and and_gate(inputs, A4, A3, A2, A1);

    assign Y = inputs & EN;

endmodule
