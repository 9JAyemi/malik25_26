module spdu_13_sva (
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
    // During reset, all outputs are driven low.
    check_reset_drives_outputs_low: assert property (
        @(posedge clk) reset |-> ##0 (out0 == 1'b0 && out1 == 1'b0 && out2 == 1'b0 && out3 == 1'b0)
    );

    // With reset low, out3 updates to ~((d3&in3) | (~d3&in2)) at the clock edge.
    check_out3_logic_equation: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |-> ##0 (out3 == ~((d3 & in3) | (~d3 & in2)))
    );

    // With reset low, out2 updates to ~((d2&in1) | (~d2&in0)) at the clock edge.
    check_out2_logic_equation: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |-> ##0 (out2 == ~((d2 & in1) | (~d2 & in0)))
    );

    // With reset low, out1 updates to ~((d1&in3) | (~d1&in2)) at the clock edge.
    check_out1_logic_equation: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |-> ##0 (out1 == ~((d1 & in3) | (~d1 & in2)))
    );

    // With reset low, out0 updates to ~((reset)|(d0&in1)|(~d0&in0)) at the clock edge.
    check_out0_logic_equation: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |-> ##0 (out0 == ~((reset) | (d0 & in1) | (~d0 & in0)))
    );

    // When d3==1, out3 equals ~in3 on the update cycle.
    check_out3_select_in3_when_d3_1: assert property (
        @(posedge clk) disable iff (reset) (d3 == 1'b1) |-> ##0 (out3 == ~in3)
    );

    // When d3==0, out3 equals ~in2 on the update cycle.
    check_out3_select_in2_when_d3_0: assert property (
        @(posedge clk) disable iff (reset) (d3 == 1'b0) |-> ##0 (out3 == ~in2)
    );

    // When d2==1, out2 equals ~in1 on the update cycle.
    check_out2_select_in1_when_d2_1: assert property (
        @(posedge clk) disable iff (reset) (d2 == 1'b1) |-> ##0 (out2 == ~in1)
    );

    // When d2==0, out2 equals ~in0 on the update cycle.
    check_out2_select_in0_when_d2_0: assert property (
        @(posedge clk) disable iff (reset) (d2 == 1'b0) |-> ##0 (out2 == ~in0)
    );

    // When d1==1, out1 equals ~in3 on the update cycle.
    check_out1_select_in3_when_d1_1: assert property (
        @(posedge clk) disable iff (reset) (d1 == 1'b1) |-> ##0 (out1 == ~in3)
    );

    // When d1==0, out1 equals ~in2 on the update cycle.
    check_out1_select_in2_when_d1_0: assert property (
        @(posedge clk) disable iff (reset) (d1 == 1'b0) |-> ##0 (out1 == ~in2)
    );

    // When d0==1, out0 equals ~in1 on the update cycle.
    check_out0_select_in1_when_d0_1: assert property (
        @(posedge clk) disable iff (reset) (d0 == 1'b1) |-> ##0 (out0 == ~in1)
    );

    // When d0==0, out0 equals ~in0 on the update cycle.
    check_out0_select_in0_when_d0_0: assert property (
        @(posedge clk) disable iff (reset) (d0 == 1'b0) |-> ##0 (out0 == ~in0)
    );
endmodule