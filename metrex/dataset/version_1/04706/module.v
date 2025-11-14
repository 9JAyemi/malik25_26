
module flip_flop (
    Q      ,
    Q_N    ,
    D      ,
    SCD    ,
    SCE    ,
    CLK_N  ,
    SET_B  ,
    RESET_B
);

    output Q      ;
    output Q_N    ;
    input  D      ;
    input  SCD    ;
    input  SCE    ;
    input  CLK_N  ;
    input  SET_B  ;
    input  RESET_B;

    reg Q = 1'b0;
    assign Q_N = ~Q;

    always @ (posedge CLK_N) begin
        if (SCD)   Q <= 1'b0;
        else if (SCE)   Q <= 1'b1;
        else if (SET_B)  Q <= 1'b1;
        else if (RESET_B) Q <= 1'b0;
        else            Q <= D;
    end

endmodule