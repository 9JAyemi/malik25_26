module signal_combiner (
    input A1,
    input A2,
    input A3,
    input B1,
    input C1,
    output Y
);

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    assign Y = (A1) ? 1 : ((A2) ? B1 : ((A3) ? C1 : 0));

endmodule