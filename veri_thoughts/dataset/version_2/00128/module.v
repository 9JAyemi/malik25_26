module mux4(
    input A0, A1, A2, A3, S0, S1, VPWR, VGND, VPB, VNB,
    output X
);

wire w1, w2, w3;

assign w1 = (~S1 & ~S0) ? A0 : (~S1 & S0) ? A1 : (S1 & ~S0) ? A2 : A3;
assign w2 = (VGND == 0) ? 0 : VPWR;
assign w3 = (VPB == 0) ? 0 : VNB;

assign X = (w1 & w2 & w3);

endmodule