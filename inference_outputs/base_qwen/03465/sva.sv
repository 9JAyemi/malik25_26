```systemverilog
module sky130_fd_sc_hvl__a22o_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    output logic X
);
    // Combinational logic: X is determined by A1, A2, B1, and B2
    // X = (A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2)
    combinational_logic: assert property (
        @(posedge clk) disable iff (!RESETn) (X == ((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2)))
    );
endmodule
```