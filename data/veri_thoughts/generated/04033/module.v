module or_gate_power_good (
    output X,
    input A, B, C, VPWR, VGND, VPB, VNB
);

    wire or_out;
    wire pg_out;

    assign or_out = A | B | C;

    assign X = (or_out & VPWR & VGND);

endmodule