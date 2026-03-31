```systemverilog
module top_module_sva (
    input logic clk,
    input logic reset,
    output logic [3:0] q
);
    // Reset behavior: q should be 0 after reset
    reset_behavior: assert property (
        @(posedge clk) disable iff (!reset) q == 4'b0000
    );
    
    // Counter increment: q should increment by 1 on each clock cycle when not reset
    increment_behavior: assert property (
        @(posedge clk) disable iff (!reset) (q inside {[0:14]}) |-> q + 1 == q
    );
    
    // Counter wrap-around: q should wrap around from 15 to 0
    wrap_around_behavior: assert property (
        @(posedge clk) disable iff (!reset) q == 4'b1111 |-> q + 1 == 4'b0000
    );
endmodule
```