```systemverilog
module sky130_fd_sc_ms__a221oi_sva (
    input logic CLK,
    input logic RESETn,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    output logic Y
);
    ///// Combinational logic /////
    // Y is the output of a NOR gate with inputs from AND gates.
    // The AND gates have inputs B1, B2 and A1, A2 respectively.
    // The NOR gate has inputs from the AND gates and C1.
    combinational_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == ~(B1 & B2 | A1 & A2 | C1))
    );
endmodule
```