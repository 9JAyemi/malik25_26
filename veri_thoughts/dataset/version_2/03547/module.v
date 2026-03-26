module sky130_fd_sc_ms__fa (
    input A,
    input B,
    input CIN,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output COUT,
    output SUM
);

    // Implementing full adder using behavioral modeling
    assign SUM = A ^ B ^ CIN;
    assign COUT = (A & B) | (B & CIN) | (A & CIN);
    
endmodule