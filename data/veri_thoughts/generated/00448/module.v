module four_input_nand (
    input A_N,
    input B_N,
    input C,
    input D,
    output Y,
    input VPWR,
    input VGND
);

    wire temp1, temp2, temp3, temp4;

    nand4bb nand1 (
        .A_N(A_N),
        .B_N(B_N),
        .C(C),
        .D(D),
        .Y(temp1),
        .VPWR(VPWR),
        .VGND(VGND)
    );

    nand4bb nand2 (
        .A_N(temp1),
        .B_N(temp1),
        .C(temp1),
        .D(temp1),
        .Y(temp2),
        .VPWR(VPWR),
        .VGND(VGND)
    );

    nand4bb nand3 (
        .A_N(temp2),
        .B_N(temp2),
        .C(temp2),
        .D(temp2),
        .Y(temp3),
        .VPWR(VPWR),
        .VGND(VGND)
    );

    nand4bb nand4 (
        .A_N(temp3),
        .B_N(temp3),
        .C(temp3),
        .D(temp3),
        .Y(Y),
        .VPWR(VPWR),
        .VGND(VGND)
    );

endmodule

module nand4bb (
    input A_N,
    input B_N,
    input C,
    input D,
    output Y,
    input VPWR,
    input VGND
);

    assign Y = ~(A_N & B_N & C & D);

endmodule