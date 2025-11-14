
module sky130_fd_sc_hd__nor4 (
    output Y,
    input A,
    input B,
    input C,
    input D,
    inout VPWR,
    inout VGND,
    inout VPB,
    inout VNB
);
    assign Y = ~((A ~^ B) ~| (C ~^ D));
endmodule
