```systemverilog
module simple_adder_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] A,
    input logic [7:0] B,
    output logic [7:0] C
);
    ///// Device reset /////
    // At reset assertion, the output C must be LOW.
    reset: assert property (
        @(posedge clk) !rst |-> (C == 8'b0)
    );

    ///// Sequential logic /////
    // C should only change on the rising edge of the clock.
    sequential_logic: assert property (
        @(posedge clk) disable iff (!rst) $stable(C)
    );

    // C should be the sum of A and B on the rising edge of the clock.
    adder_behavior: assert property (
        @(posedge clk) disable iff (!rst) C == A + B
    );
endmodule
```