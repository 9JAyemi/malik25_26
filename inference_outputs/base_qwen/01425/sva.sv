```systemverilog
module sky130_fd_sc_lp__a311oi_sva (
    input logic CLK,
    input logic RESETn,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    output logic Y
);
    // Combinational logic: Y is driven by the output of the NOR gate
    // The NOR gate's input is the output of the AND gate
    // The AND gate's inputs are A3, A1, and A2
    // The NOR gate's inputs are the AND gate's output, B1, and C1
    // The buffer drives the output Y
    combinational_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == ~(A3 & A1 & A2 | B1 | C1))
    );
endmodule
```