```systemverilog
module nand_decoder_sva (
    input logic [1:0] in,
    input logic [3:0] out
);
    // NAND operation on inputs
    nand_operation: assert property (
        @(posedge CLK) disable iff (!RESETn) (out[0] == ~in[0] & ~in[1]) && (out[1] == ~in[0] & ~in[1]) && (out[2] == ~in[0] & ~in[1]) && (out[3] == ~in[0] & ~in[1])
    );
    // Each output is the negation of the NAND result
    negation_operation: assert property (
        @(posedge CLK) disable iff (!RESETn) (out[0] == ~out[0]) && (out[1] == ~out[1]) && (out[2] == ~out[2]) && (out[3] == ~out[3])
    );
endmodule
```