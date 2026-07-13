
module sky130_fd_sc_hs__sdfxbp_2 (
    CLK,
    D  ,
    Q  ,
    Q_N,
    SCD,
    SCE
);

    input  CLK;
    input  D  ;
    output Q  ;
    output Q_N;
    input  SCD;
    input  SCE;

    wire Q_reg;
    wire Q_N_reg;

    assign Q = Q_reg;
    assign Q_N = Q_N_reg;

    sdfxbp base (
        .CLK(CLK),
        .D(D),
        .Q(Q_reg),
        .Q_N(Q_N_reg),
        .SCD(SCD),
        .SCE(SCE)
    );


endmodule
module sdfxbp (
    input CLK,   // Clock input
    input D,     // Data input
    output Q,    // Normal output
    output Q_N,  // Inverted output
    input SCD,   // Scan chain data input
    input SCE    // Scan chain enable input
);

    reg Q_internal;

    assign Q = Q_internal;
    assign Q_N = ~Q_internal;

    // Update flip-flop state at rising edge of clock
    always @(posedge CLK) begin
        if (SCE)
            // When scan chain is enabled, load scan chain data
            Q_internal <= SCD;
        else
            // Otherwise, load data from D input
            Q_internal <= D;
    end

endmodule