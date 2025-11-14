module voltage_inverter (
    output Z,
    input A,
    input TE
);

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB;
    supply0 VNB;

    // p-type and n-type transistors
    //sky130_fd_sc_hdll_vnp vnp (
    //    .D(Z),
    //    .G(A),
    //    .S(VPB),
    //    .B(VNB)
    //);
    //sky130_fd_sc_hdll_vpp vpp (
    //    .D(Z),
    //    .G(A),
    //    .S(VPB),
    //    .B(VNB)
    //);

    // inverter logic
    assign Z = TE ? ~A : A;

endmodule