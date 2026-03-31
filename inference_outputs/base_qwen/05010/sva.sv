```systemverilog
module sky130_fd_sc_lp__and4_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    output logic X
);
    // Combinational logic: X is the output of an AND gate followed by a buffer.
    // Ensure that X is only driven by the AND gate output.
    combinational_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) X |-> (X == (A & B & C & D))
    );
endmodule
```