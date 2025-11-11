module sky130_fd_sc_hs__sdlclkp (
    GCLK,
    GATE,
    CLK ,
    SCE
);

    output GCLK;
    input  GATE;
    input  CLK ;
    input  SCE ;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;

    reg gate_state;

    always @ (posedge SCE)
    begin
        gate_state <= GATE;
    end

    assign GCLK = (gate_state == 1'b1) ? CLK : 1'b0;

endmodule