
module d_ff_reset (
    input D,
    input RESET_B,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    input CLK_N,
    output reg Q
);

    wire D_valid;
    wire RESET_B_valid;
    wire VPWR_valid;
    wire VGND_valid;
    wire VPB_valid;
    wire VNB_valid;

    assign D_valid = (VPWR == 1'b1) && (VGND == 1'b0);
    assign RESET_B_valid = (VPWR == 1'b1) && (VGND == 1'b0);
    assign VPWR_valid = (VPWR == 1'b1) && (VGND == 1'b0);
    assign VGND_valid = (VPWR == 1'b1) && (VGND == 1'b0);
    assign VPB_valid = (VPB == 1'b1) && (VNB == 32'b11111111111111111111111111111111);
    assign VNB_valid = (VPB == 1'b1) && (VNB == 32'b11111111111111111111111111111111);

    always @(posedge CLK_N) begin
        if (RESET_B_valid && !RESET_B) begin
            Q <= 1'b0;
        end else if (D_valid) begin
            Q <= D;
        end
    end

endmodule
