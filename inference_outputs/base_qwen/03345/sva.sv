```systemverilog
module sky130_fd_sc_hvl__a21oi_sva (
    input logic CLK,
    input logic RESETn,
    input logic A1,
    input logic A2,
    input logic B1,
    output logic Y
);
    // Combinational logic: Y is driven by the output of the NOR gate
    // The NOR gate's input is the AND of A1 and A2
    combinational_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) Y |-> (B1 == 1'b1) && (A1 == 1'b0) && (A2 == 1'b0)
    );
    // Combinational logic: Y is driven by the output of the NOR gate
    // The NOR gate's input is the AND of A1 and A2
    combinational_logic_2: assert property (
        @(posedge CLK) disable iff (!RESETn) !Y |-> (B1 == 1'b0) || (A1 == 1'b1) || (A2 == 1'b1)
    );
endmodule
```