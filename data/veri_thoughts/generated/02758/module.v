
module sky130_fd_sc_ms__sdfbbn (
    D      , // moved to the beginning of the list
    SCD    ,
    SCE    ,
    CLK    ,
    SET_B  ,
    RESET_B,
    Q      ,
    Q_N    ,
    VPWR   ,
    VGND   ,
    VPB    ,
    VNB
);

    input  D      ;
    input  SCD    ;
    input  SCE    ;
    input  CLK    ;
    input  SET_B  ;
    input  RESET_B;
    output Q      ;
    output Q_N    ;
    input  VPWR   ;
    input  VGND   ;
    input  VPB    ;
    input  VNB    ;

    reg Q_N;  // Removed assignment to Q_N from reg type to wire type

    // Inverted the Q output to match the Q_N output
    assign Q = ~Q_N;

    reg [1:0] state;

    always @ (posedge CLK) begin
        if (SET_B == 1'b0) begin
            Q_N <= 1'b1;
        end
        if (RESET_B == 1'b0) begin
            Q_N <= 1'b0;
        end
        if (SCE) begin
            Q_N <= D;
        end
        if (SCD) begin
            Q_N <= 1'b0;
        end
    end

endmodule
