module binary_counter_sva
#(
  parameter N = 4
)
(
  input clk,
  input reset,
  output reg [N-1:0] count
);

    ///// Device reset /////
    // At reset assertion, the counter must be driven to 0.
    reset: assert property (
        @(posedge clk) reset |-> (count == 0)
    );

    ///// Counter behavior /////
    // The counter should increment by 1 on each positive edge of the clock.
    counter_increment: assert property (
        @(posedge clk) disable iff (reset) count == count + 1
    );

endmodule