module digital_circuit (
    input  D   ,
    output Q   ,
    output Q_N ,
    input  SCD ,
    input  SCE ,
    input  CLK ,
    input  VPB ,
    input  VPWR,
    input  VGND,
    input  VNB
);

wire D_ff;
reg Q_ff;
wire Q_N_ff;

assign D_ff = SCE ? SCD : D;

always @(posedge CLK) begin
    Q_ff <= D_ff;
end

assign Q = Q_ff;
assign Q_N = ~Q_ff;

endmodule