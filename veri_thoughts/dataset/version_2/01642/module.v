module generate_output_signals(input VPWR, input VGND, output VDD, output VSS, output VDD_VSS);

    assign VDD = (VPWR == 1'b1 && VGND == 1'b0) ? 1'b1 : 1'b0;
    assign VSS = (VGND == 1'b1 && VPWR == 1'b0) ? 1'b1 : 1'b0;
    assign VDD_VSS = (VDD == 1'b1 && VSS == 1'b1) ? 1'b1 : 1'b0;

endmodule
