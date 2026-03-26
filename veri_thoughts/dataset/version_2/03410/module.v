
module sky130_fd_sc_ms__a211o (
    X,
    A1,
    A2,
    B1,
    C1
);

    output X;
    input  A1;
    input  A2;
    input  B1;
    input  C1;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB;
    supply0 VNB;

    // Instantiate the base cell
    sky130_fd_sc_ms__a211o_cell base_cell (
        .X(X),
        .A1(A1),
        .A2(A2),
        .B1(B1),
        .C1(C1)
    );

endmodule

module sky130_fd_sc_ms__a211o_cell (
    X,
    A1,
    A2,
    B1,
    C1
);

    output X;
    input  A1;
    input  A2;
    input  B1;
    input  C1;

    // RTL implementation of the cell
    assign X = (A1 & A2) | (B1 & C1);

endmodule
