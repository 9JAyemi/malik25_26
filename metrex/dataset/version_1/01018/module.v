module flip_flop (
    Q      ,
    Q_N    ,
    D      ,
    SCD    ,
    SCE    ,
    CLK    ,
    SET_B  ,
    RESET_B,
    VPWR   ,
    VGND   ,
    VPB    ,
    VNB
);

    output Q      ;
    output Q_N    ;
    input  D      ;
    input  SCD    ;
    input  SCE    ;
    input  CLK    ;
    input  SET_B  ;
    input  RESET_B;
    input  VPWR   ;
    input  VGND   ;
    input  VPB    ;
    input  VNB    ;
    
    reg Q;
    assign Q_N = ~Q;
    
    always @(posedge CLK) begin
        if (SET_B == 0) begin
            Q <= 1;
        end else if (RESET_B == 0) begin
            Q <= 0;
        end else if (SCD == 0) begin
            Q <= 0;
        end else if (SCE == 1) begin
            Q <= D;
        end
    end
    
endmodule