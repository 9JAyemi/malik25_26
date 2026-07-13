module mux2 (
    input A0,
    input A1,
    input S,
    output X,
    input VPB,
    input VPWR,
    input VGND,
    input VNB
);

assign X = (S == 1) ? A1 : A0;

endmodule