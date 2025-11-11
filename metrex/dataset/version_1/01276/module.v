
module mux4to1 (
    input in0,
    input in1,
    input in2,
    input in3,
    input sel0,
    input sel1,
    output out,
    inout VPWR,
    inout VGND,
    inout VPB,
    inout VNB
);

    assign out = (sel1 & (sel0 & in0 | ~sel0 & in1)) | (~sel1 & (sel0 & in2 | ~sel0 & in3));

endmodule
