module my_dff_reset (
    output reg Q,
    input CLK,
    input D,
    input RESET_B,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    always @(posedge CLK or negedge RESET_B)
    begin
        if (!RESET_B)
            Q <= 1'b0;
        else
            Q <= D;
    end

endmodule