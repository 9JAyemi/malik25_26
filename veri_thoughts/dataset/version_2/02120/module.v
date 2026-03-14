module combinational_logic (
    input A1,
    input A2,
    input A3,
    input B1,
    input VPB,
    output X,
    input VPWR,
    input VGND,
    input VNB
);

    assign X = (A1 & A2 & A3) | (B1 & VPB);

endmodule