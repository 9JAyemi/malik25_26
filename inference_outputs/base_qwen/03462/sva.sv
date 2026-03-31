```systemverilog
module oh_mux8_sva (
    input logic clk,
    input logic rst_n,
    input logic sel7,
    input logic sel6,
    input logic sel5,
    input logic sel4,
    input logic sel3,
    input logic sel2,
    input logic sel1,
    input logic sel0,
    input [DW-1:0] in7,
    input [DW-1:0] in6,
    input [DW-1:0] in5,
    input [DW-1:0] in4,
    input [DW-1:0] in3,
    input [DW-1:0] in2,
    input [DW-1:0] in1,
    input [DW-1:0] in0,
    output [DW-1:0] out
);
    // The output should be one of the inputs selected by the selector signals.
    mux_output: assert property (
        @(posedge clk) disable iff (!rst_n) out == ({(DW){sel0}} & in0[DW-1:0] |
                                                       {(DW){sel1}} & in1[DW-1:0] |
                                                       {(DW){sel2}} & in2[DW-1:0] |
                                                       {(DW){sel3}} & in3[DW-1:0] |
                                                       {(DW){sel4}} & in4[DW-1:0] |
                                                       {(DW){sel5}} & in5[DW-1:0] |
                                                       {(DW){sel6}} & in6[DW-1:0] |
                                                       {(DW){sel7}} & in7[DW-1:0])
    );
endmodule
```