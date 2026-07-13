module my_circuit (
    Q    ,
    CLK  ,
    D    ,
    SCD  ,
    SCE  ,
    SET_B,
    VPWR ,
    VGND ,
    VPB  ,
    VNB
);

    output Q    ;
    input  CLK  ;
    input  D    ;
    input  SCD  ;
    input  SCE  ;
    input  SET_B;
    input  VPWR ;
    input  VGND ;
    input  VPB  ;
    input  VNB  ;

    reg Q_reg;

    always @(posedge CLK) begin
        if (SET_B) begin
            Q_reg <= 1;
        end else if (SCD) begin
            Q_reg <= D;
        end else if (SCE) begin
            Q_reg <= 0;
        end
    end

    assign Q = Q_reg;

endmodule