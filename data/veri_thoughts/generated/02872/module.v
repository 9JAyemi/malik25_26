
module flip_flop(input D, SCD, SCE, RESET_B, VPWR, VGND, VPB, VNB, output Q, input CLK);

    // Instantiate the DFF module
    DFF dff(D, SCD, SCE, RESET_B, Q, CLK);

endmodule

module DFF(input D, SCD, SCE, RESET_B, output Q, input CLK);
    
    reg q;
    
    always @(posedge CLK or negedge RESET_B)
    begin
        if (!RESET_B)
            q <= 1'b0;
        else if (SCE)
            q <= D;
    end
    
    assign Q = q;
    
endmodule
