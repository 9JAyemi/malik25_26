module sky130_fd_sc_hs__a222o_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2,
    output logic X
);
    // Combinational logic: X is determined by the inputs A1, A2, B1, B2, and C1, C2
    // X = 1 if (A1 & A2) | (B1 & B2) | (~C1 & ~C2), otherwise X = 0
    combinational_logic: assert property (
        @(posedge clk) disable iff (!RESETn) (X == ((A1 & A2) | (B1 & B2) | (~C1 & ~C2)))
    );
endmodule