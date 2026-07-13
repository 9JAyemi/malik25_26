module sky130_fd_sc_hd__o221ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);
    // Combinational logic: Y is the output of a NAND gate with inputs from OR gates
    // The OR gates have inputs from A1, A2, B1, and B2
    // The NAND gate also has an additional input from C1
    combinational_logic: assert property (
        @(posedge clk) disable iff (!RESETn) (Y == ~(A1 | A2 & B1 | B2 & C1))
    );
endmodule