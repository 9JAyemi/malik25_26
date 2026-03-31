```systemverilog
module counter_4bit_async_reset_sva (
    input logic clk,
    input logic rst,
    output logic [3:0] count
);
    ///// Asynchronous reset behavior /////
    // At reset assertion, count must be driven to 0.
    reset: assert property (
        @(posedge clk) !rst |-> (count == 4'b0)
    );

    ///// Sequential logic behavior /////
    // Count should increment by 1 on each positive edge of the clock.
    count_increment: assert property (
        @(posedge clk) disable iff (!rst) count == count + 1
    );
endmodule
```