```systemverilog
module sky130_fd_sc_ls__ha_sva (
    input logic CLK,
    input logic A,
    input logic B,
    output logic COUT,
    output logic SUM
);
    // COUT is the result of the AND operation between A and B
    and_operation: assert property (
        @(posedge CLK) disable iff (!CLK) (COUT == (A & B))
    );

    // SUM is the result of the XOR operation between A and B
    xor_operation: assert property (
        @(posedge CLK) disable iff (!CLK) (SUM == (A ^ B))
    );
endmodule
```