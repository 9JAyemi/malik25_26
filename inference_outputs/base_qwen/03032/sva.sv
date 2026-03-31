```systemverilog
module binary_counter_sva (
    input logic clk,
    input logic rst,
    output logic [3:0] count
);
    ///// Device reset /////
    // At reset assertion, the counter must be driven to 0.
    reset: assert property (
        @(posedge clk) rst |-> (count == 4'b0)
    );

    ///// Counter behavior /////
    // The counter should increment by 1 on each positive edge of the clock.
    counter_increment: assert property (
        @(posedge clk) disable iff (rst) count == count + 1
    );
endmodule
```