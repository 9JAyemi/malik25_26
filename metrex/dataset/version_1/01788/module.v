module communication_module (
    input A1,
    input A2,
    input A3,
    input B1,
    input VPWR,
    input VGND,
    output reg X
);

    wire o31a_out;
    //sky130_fd_sc_hs__o31a base (
    //    .X(o31a_out),
    //    .A1(A1),
    //    .A2(A2),
    //    .A3(A3),
    //    .B1(B1),
    //    .VPWR(VPWR),
    //    .VGND(VGND)
    //);

    always @* begin
        X = (A1 & A2 & A3 & ~B1) ? 1'b1 : 1'b0;
    end

endmodule