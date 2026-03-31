```systemverilog
module up_counter_sva(clk, rst_n, count);
    input logic clk, rst_n;
    input logic [15:0] count;
    
    // At reset assertion, the counter must be driven to 0.
    reset: assert property (
        @(posedge clk) !rst_n |-> (count == 16'b0000000000000000)
    );
    
    // The counter should increment by 1 on each positive edge of the clock.
    increment: assert property (
        @(posedge clk) disable iff (!rst_n) count == count + 1'b1
    );
endmodule
```