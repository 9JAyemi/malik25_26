module my_module_sva (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic d0,
    input logic d1,
    input logic d2,
    input logic d3,
    input logic clk,
    input logic reset,
    input logic out0,
    input logic out1,
    input logic out2,
    input logic out3
);

    // With d0 low, out0 selects in0.
    check_out0_select_in0: assert property (
        @(posedge clk) disable iff (reset) (!d0) |-> (out0 == in0)
    );

    // With d0 high, out0 selects in1.
    check_out0_select_in1: assert property (
        @(posedge clk) disable iff (reset) d0 |-> (out0 == in1)
    );

    // With d1 low, out1 selects in2.
    check_out1_select_in2: assert property (
        @(posedge clk) disable iff (reset) (!d1) |-> (out1 == in2)
    );

    // With d1 high, out1 selects in3.
    check_out1_select_in3: assert property (
        @(posedge clk) disable iff (reset) d1 |-> (out1 == in3)
    );

    // A high reset drives out2 low on the next clock.
    check_out2_reset_forces_low: assert property (
        @(posedge clk) reset |=> (out2 == 1'b0)
    );

    // With reset low and d2 low, out2 captures the inverse of in0.
    check_out2_select_in0: assert property (
        @(posedge clk) (!reset && !d2) |=> (out2 == ~$past(in0))
    );

    // With reset low and d2 high, out2 captures the inverse of in1.
    check_out2_select_in1: assert property (
        @(posedge clk) (!reset && d2) |=> (out2 == ~$past(in1))
    );

    // With d3 low, out3 captures in2 on the next clock.
    check_out3_select_in2: assert property (
        @(posedge clk) (!d3) |=> (out3 == $past(in2))
    );

    // With d3 high, out3 captures in3 on the next clock.
    check_out3_select_in3: assert property (
        @(posedge clk) d3 |=> (out3 == $past(in3))
    );

endmodule