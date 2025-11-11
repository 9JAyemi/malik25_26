
module sky130_fd_sc_hs__dfsbp (
    VPWR ,
    VGND ,
    Q    ,
    Q_N  ,
    CLK  ,
    D    ,
    SET_B
);

    // Module ports
    input  VPWR ;
    input  VGND ;
    output Q    ;
    output Q_N  ;
    input  CLK  ;
    input  D    ;
    input  SET_B;

    // Local signals
    reg    buf_Q        ;
    wire   SET          ;
    reg    notifier     ;
    wire   D_delayed    ;
    wire   SET_B_delayed;
    wire   CLK_delayed  ;
    wire   awake        ;
    wire   cond0        ;
    wire   cond1        ;

    // Additions
    assign D_delayed = D;
    assign SET_B_delayed = SET_B;
    assign CLK_delayed = CLK;
    assign SET = ~SET_B_delayed;
    assign awake = (VPWR === 1'b1 );
    assign cond0 = (SET_B_delayed === 1'b1 );
    assign cond1 = (SET_B === 1'b1 );

    always @(posedge CLK_delayed or negedge awake) begin
        if (!awake) begin
            buf_Q <= 1'b0;
            notifier <= 1'b0;
        end else if (!cond0 || !cond1) begin
            buf_Q <= 1'b1;
            notifier <= 1'b1;
        end else if (notifier) begin
            buf_Q <= D_delayed;
            notifier <= 1'b0;
        end
    end

    buf buf0 (Q     , buf_Q                                            );
    not not1 (Q_N   , buf_Q                                            );

endmodule
