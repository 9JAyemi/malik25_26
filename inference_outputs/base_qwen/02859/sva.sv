```systemverilog
module and4bb_sva (
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    output logic X
);
    // Combinational logic: X is the AND of A_N, B_N, C, and D
    comb_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) (X == (A_N & B_N & C & D))
    );
endmodule
```