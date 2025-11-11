
module sky130_fd_sc_ls__o21ai_2 (
    Y,
    A1,
    A2,
    B1,
    VPWR,
    VGND,
    VPB,
    VNB
);

    output Y;
    input A1;
    input A2;
    input B1;
    input VPWR;
    input VGND;
    input VPB;
    input VNB;

endmodule

module my_module(
    out_wire,
    in_wire1,
    in_wire2,
    in_wire3,
    power,
    ground,
    power_bond,
    ground_bond
);

    output out_wire;
    input in_wire1;
    input in_wire2;
    input in_wire3;
    input power;
    input ground;
    input power_bond;
    input ground_bond;

    wire Y;
    sky130_fd_sc_ls__o21ai_2 base (
        .Y(Y),
        .A1(in_wire1),
        .A2(in_wire2),
        .B1(in_wire3),
        .VPWR(power),
        .VGND(ground),
        .VPB(power_bond),
        .VNB(ground_bond)
    );

    assign out_wire = (in_wire1 & ~in_wire2 & ~in_wire3) |
                      (~in_wire1 & in_wire2 & ~in_wire3) |
                      (~in_wire1 & in_wire2 & in_wire3) |
                      (~in_wire1 & ~in_wire2 & in_wire3);

endmodule
