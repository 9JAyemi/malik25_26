
module my_module (
    Q   ,
    CLK ,
    D   ,
    DE  ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output Q   ;
    input  CLK ;
    input  D   ;
    input  DE  ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;
    
    reg Q_reg;
    always @ (posedge CLK) begin
        if (DE) begin
            Q_reg <= D;
        end
    end
    
    assign Q = DE ? Q_reg : Q_reg;
    
endmodule