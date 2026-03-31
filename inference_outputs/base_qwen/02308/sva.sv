```systemverilog
module nand2_module_sva (
    input logic in1,
    input logic in2,
    input logic clk,
    output logic out
);
    // NAND operation on inputs in1 and in2
    nand_operation: assert property (
        @(posedge clk) disable iff (!clk) out == ~(in1 & in2)
    );
endmodule
```