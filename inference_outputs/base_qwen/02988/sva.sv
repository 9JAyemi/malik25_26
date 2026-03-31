```systemverilog
module RegisterAdd_4_sva (
    input logic CLK,
    input logic reset,
    input logic [3:0] in1,
    input logic [3:0] in2,
    output logic [3:0] out
);
    // At reset, the output should be 0
    reset_output: assert property (
        @(posedge CLK) disable iff (!reset) (reset |-> out == 4'd0)
    );

    // The output should be the sum of in1 and in2 when not in reset
    add_behavior: assert property (
        @(posedge CLK) disable iff (!reset) (!reset |-> out == in1 + in2)
    );
endmodule
```