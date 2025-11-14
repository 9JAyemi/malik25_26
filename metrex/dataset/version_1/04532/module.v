module and_gate_with_control (
    input A1,
    input A2,
    input C1,
    output Y
);

    assign Y = (C1 == 0) ? (A1 & A2) : 0;

endmodule