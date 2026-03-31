```systemverilog
module up_counter_sva (
    input logic clk,
    input logic reset,
    output logic [3:0] count,
    output logic out
);
    ///// Counter reset /////
    // At reset, the counter must be driven to 0.
    reset_count: assert property (
        @(posedge clk) disable iff (!reset) (reset |-> count == 4'b0)
    );

    ///// Counter increment /////
    // The counter must increment by 1 on each clock cycle when reset is low.
    increment_count: assert property (
        @(posedge clk) disable iff (!reset) (!reset |-> count == count + 1)
    );

    ///// Output toggle /////
    // The output must toggle on each clock cycle when reset is low.
    toggle_out: assert property (
        @(posedge clk) disable iff (!reset) (!reset |-> out == ~out)
    );
endmodule
```