module fill_diode (
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output fill
);

assign fill = (VPWR & !VGND) | (!VPB & VNB);

endmodule