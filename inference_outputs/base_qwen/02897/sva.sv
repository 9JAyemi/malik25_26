```systemverilog
module mux4_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic sel0,
    input logic sel1,
    output logic [3:0] out
);
    // The logic is purely combinational as there is no clock signal.
    // No reset signal is present in the RTL.

    // The output is a multiplexer of four inputs based on the selection signals.
    // The output should be one of the inputs selected by sel0 and sel1.
    mux_output: assert property (
        @(posedge clk) disable iff (!RESETn) out == (sel1 & sel0 ? in3 : sel1 & ~sel0 ? in2 : ~sel1 & sel0 ? in1 : in0)
    );
endmodule
```