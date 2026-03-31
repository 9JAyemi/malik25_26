```systemverilog
module and4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    output logic X
);
    // No clock or reset signals in this combinational logic module

    // Combinational logic behavior: X is the AND of A, B, C, and D
    comb_logic: assert property (
        @(posedge clk) disable iff (!RESETn) (X == (A & B & C & D))
    );
endmodule
```