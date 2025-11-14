
module sky130_fd_sc_dff (
    Q      , //output
    CLK_N  , //input 
    D      , //input 
    RESET_B, //input 
    VPWR   , //input 
    VGND   , //input 
    VPB    , //input 
    VNB    //input 
);

    output Q      ;
    input  CLK_N  ;
    input  D      ;
    input  RESET_B;
    input  VPWR   ;
    input  VGND   ;
    input  VPB    ;
    input  VNB    ;

    reg Q_int; //internal register

    assign Q = Q_int; // assign the output to the internal wire

    // Define the D-flip-flop using Verilog primitives
    always @(posedge CLK_N or negedge RESET_B) begin
        if (!RESET_B)
            Q_int <= 1'b0; // set Q to 0 when reset is active
        else
            Q_int <= D;    //otherwise set Q to D
    end

endmodule

module asynchronous_reset_flip_flop (
    Q      , //output
    CLK_N  , //input 
    D      , //input 
    RESET_B, //input 
    VPWR   , //input 
    VGND   , //input 
    VPB    , //input 
    VNB    //input 
);

    output Q      ;
    input  CLK_N  ;
    input  D      ;
    input  RESET_B;
    input  VPWR   ;
    input  VGND   ;
    input  VPB    ;
    input  VNB    ;

    wire Q_next; //internal wire

    assign Q = Q_next; // assign the output to the internal wire

    sky130_fd_sc_dff dff (
        .Q      (Q_next), //connect internal wire of DFF to internal wire of this module
        .CLK_N  (CLK_N),
        .D      (D),
        .RESET_B(RESET_B),
        .VPWR   (VPWR),
        .VGND   (VGND),
        .VPB    (VPB),
        .VNB    (VNB)
    );
endmodule
