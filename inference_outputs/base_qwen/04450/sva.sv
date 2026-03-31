```systemverilog
module flip_flop_sva (
    input logic CLK,
    input logic DE,
    input logic SCE,
    input logic SCD,
    output logic Q
);
    // Sequential logic update rule
    seq_update: assert property (
        @(posedge CLK) disable iff (!CLK) (DE |-> Q == D) && (SCE |-> Q == SCD)
    );
endmodule
```