```systemverilog
module sky130_fd_sc_hdll__a221oi_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    output logic Y
);
    // Combinational logic: Y is driven by the output of the NOR gate
    // The NOR gate's input is the AND of B1 and B2, and the AND of A1 and A2
    // The NOR gate also takes C1 as an input
    combinational_logic: assert property (
        @(posedge clk) disable iff (!RESETn) (Y == ~(B1 & B2 & A1 & A2 & C1))
    );
endmodule
```