```systemverilog
module RCB_FRL_TrainingPattern_sva (
    input logic CLK,
    input logic RST,
    output logic [7:0] DATA_OUT
);
    // Reset behavior: DATA_OUT should be 0 after reset
    reset: assert property (
        @(posedge CLK) disable iff (!RST) DATA_OUT == 8'h00
    );

    // Sequential logic behavior: DATA_OUT toggles between 0xf4 and 0xc2
    toggle: assert property (
        @(posedge CLK) disable iff (!RST) (DATA_OUT == 8'hf4) |-> DATA_OUT == 8'hc2
    );
endmodule
```