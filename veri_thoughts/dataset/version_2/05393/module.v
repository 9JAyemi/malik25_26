
module binary_dff_set (
    input  D    ,
    output Q    ,
    output Q_N  ,
    input  SET_B,
    input  CLK  ,
    input  VPB  ,
    input  VPWR ,
    input  VGND ,
    input  VNB
);

    reg D_reg;
    always @(*) begin
        D_reg = D;
    end

    reg Q_reg;
    always @(posedge CLK) begin
        if (SET_B) begin
            Q_reg <= 1'b1;
        end else begin
            Q_reg <= D_reg;
        end
    end

    assign Q = Q_reg;
    assign Q_N = ~Q_reg;

endmodule