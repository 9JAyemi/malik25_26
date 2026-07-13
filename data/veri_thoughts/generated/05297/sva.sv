module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [1:0] counter,
    input logic a,
    input logic b,
    input logic out
);

    // out is 0 on the cycle reset is released.
    check_out_release_cycle_zero: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> (out == 1'b0)
    );

    // out is 1 one cycle after reset is released.
    check_out_1_cycle_after_release: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> ##1 (out == 1'b1)
    );

    // out is 0 two cycles after reset is released.
    check_out_2_cycles_after_release: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> ##2 (out == 1'b0)
    );

    // out is 1 three cycles after reset is released.
    check_out_3_cycles_after_release: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> ##3 (out == 1'b1)
    );

    // out is 1 four cycles after reset is released.
    check_out_4_cycles_after_release: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> ##4 (out == 1'b1)
    );

    // out is 0 five cycles after reset is released.
    check_out_5_cycles_after_release: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> ##5 (out == 1'b0)
    );

    // out is 1 six cycles after reset is released.
    check_out_6_cycles_after_release: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> ##6 (out == 1'b1)
    );

    // out is 0 seven cycles after reset is released.
    check_out_7_cycles_after_release: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> ##7 (out == 1'b0)
    );

    // out is 0 eight cycles after reset is released after counter wrap.
    check_out_8_cycles_after_release: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> ##8 (out == 1'b0)
    );

    // out follows the full 9-sample sequence after reset release.
    check_full_sequence_after_release: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> (out == 1'b0) ##1
                        (out == 1'b1) ##1
                        (out == 1'b0) ##1
                        (out == 1'b1) ##1
                        (out == 1'b1) ##1
                        (out == 1'b0) ##1
                        (out == 1'b1) ##1
                        (out == 1'b0) ##1
                        (out == 1'b0)
    );

endmodule