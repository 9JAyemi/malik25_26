module my_module (
    output Y,
    input A1,
    input A2,
    input A3,
    input B1
);

    // Module supplies
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB;
    supply0 VNB;

    // Local signals
    wire and_out;
    wire nor_out;

    // AND gate
    and and_gate(
        and_out,
        A1,
        A2,
        A3
    );

    // NOR gate
    nor nor_gate(
        nor_out,
        and_out,
        B1
    );

    // Output buffer
    buf buf_gate(
        Y,
        nor_out
    );

endmodule