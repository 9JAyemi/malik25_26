
module d_ff_with_async_reset_set (
    Q    ,
    CLK  ,
    D    ,
    SET_B,
    RESET_B
);

    output Q    ;
    input  CLK  ;
    input  D    ;
    input  SET_B;
    input  RESET_B;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    reg Q;

    always @(posedge CLK) begin
        if (RESET_B) begin
            Q <= 1'b0;
        end else if (SET_B) begin
            Q <= 1'b1;
        end else begin
            Q <= D;
        end
    end

endmodule