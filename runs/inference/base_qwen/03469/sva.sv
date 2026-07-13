module mux_4to1_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [1:0] SEL,
    output logic Y
);
    // Mux output is determined by the SEL signal
    mux_output: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == (SEL == 2'b00 ? A : (SEL == 2'b01 ? B : (SEL == 2'b10 ? C : D))))
    );
endmodule