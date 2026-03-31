```systemverilog
module sky130_fd_sc_hd__a221oi_sva (
    input logic CLK,
    input logic RESETn,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    output logic Y
);
    // Combinational logic: Y is driven by the output of the NOR gate
    // The NOR gate's inputs are the outputs of two AND gates
    // The AND gates' inputs are A1, A2 and B1, B2 respectively
    // The NOR gate also has C1 as one of its inputs
    combinational_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) Y == ~(A1 & A2 | B1 & B2 | C1)
    );
endmodule
```