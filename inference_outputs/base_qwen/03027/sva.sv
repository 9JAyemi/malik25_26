module sky130_fd_sc_lp__o31a_sva (
    input logic CLK,
    input logic RESETn,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    output logic X
);
    // Combinational logic: X is driven by the output of the AND gate
    // The AND gate's input is the output of the OR gate
    // The OR gate's inputs are A2, A1, and A3
    // The AND gate's input is also B1
    // The output of the AND gate is buffered to X
    combinational_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) X == (A2 | A1 | A3) & B1
    );
endmodule