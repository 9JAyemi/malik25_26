module my_ff (
    input  D    ,
    output Q    ,
    input  SET_B,
    input  CLK
);

    supply1 VPWR;
    supply0 VGND;

    reg Q_reg;

    always @(posedge CLK) begin
        if (SET_B == 1'b1) begin
            Q_reg <= 1'b0;
        end else begin
            Q_reg <= D;
        end
    end

    assign Q = Q_reg;

endmodule