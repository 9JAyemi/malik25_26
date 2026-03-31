module RegisterAdd_4_sva (
    input logic CLK,
    input logic reset,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] out
);

    // Synchronous reset clears the register on the next clock.
    check_reset_clears_out: assert property (
        @(posedge CLK) reset |=> (out == 4'd0)
    );

    // When reset is low, out captures the previous cycle's in1+in2.
    check_loads_sum_when_not_reset: assert property (
        @(posedge CLK) disable iff (reset) 1'b1 |=> (out == ($past(in1) + $past(in2)))
    );

    // The first cycle after reset deasserts still sees out at zero.
    check_post_reset_zero: assert property (
        @(posedge CLK) disable iff (reset) $fell(reset) |-> (out == 4'd0)
    );

endmodule