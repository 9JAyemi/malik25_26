```systemverilog
module dff_en_sva (
    input logic CLK,
    input logic RESETn,
    input logic D,
    input logic E,
    output logic Q
);
    // Sequential logic: Q should only change on the rising edge of CLK when E is high.
    sequential_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) (E == 1'b1) |-> ##1 Q == D
    );
    // At reset, Q should be low.
    reset: assert property (
        @(posedge CLK) !RESETn |-> Q == 1'b0
    );
endmodule
```