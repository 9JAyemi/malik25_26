module d_ff_reset (
    input D,
    input RESET_B,
    input GATE,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output reg Q
);

    reg Q_reg;
    
    always @(posedge GATE or negedge RESET_B)
    begin
        if (!RESET_B)
            Q_reg <= 1'b0;
        else
            Q_reg <= D;
    end

    always @*
    begin
        Q = Q_reg;
    end

endmodule