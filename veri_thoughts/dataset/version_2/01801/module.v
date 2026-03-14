module flip_flop (
    output Q   ,
    output Q_N ,
    input  CLK ,
    input  D   ,
    input  SCD ,
    input  SCE ,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB 
);

    reg Q;
    wire Q_N;
    
    assign Q_N = ~Q;
    
    always @(posedge CLK) begin
        if (SCD && ~SCE) begin
            Q <= 1'b1;
        end else if (~SCD && SCE) begin
            Q <= 1'b0;
        end else if (~SCD && ~SCE) begin
            Q <= D;
        end else if (SCD && SCE) begin
            Q <= 1'b0;
        end
    end
    
endmodule