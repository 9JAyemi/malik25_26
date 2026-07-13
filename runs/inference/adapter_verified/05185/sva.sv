module FP16RAddSubS2Of5_sva (
    input logic        clk,
    input logic        rst,
    input logic        arg_0,
    input logic        arg_1,
    input logic [20:0] arg_2,
    input logic [20:0] arg_3,
    input logic [4:0]  arg_4,
    input logic        arg_5,
    input logic        arg_6,
    input logic [21:0] ret_0,
    input logic        ret_1,
    input logic        ret_2,
    input logic [4:0]  ret_3,
    input logic        ret_4,
    input logic        ret_5
);

// Reset clears the internal state and output fields.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |=> (ret_0 == 22'd0) &&
                               (ret_1 == 1'b0) &&
                               (ret_2 == 1'b0) &&
                               (ret_3 == 5'd0) &&
                               (ret_4 == 1'b0) &&
                               (ret_5 == 1'b0)
    );

// ret_1 is a direct copy of arg_0.
    check_ret1_passthrough: assert property (
        @(posedge clk) disable iff (rst) ret_1 == arg_0
    );

// ret_2 is a direct copy of arg_1.
    check_ret2_passthrough: assert property (
        @(posedge clk) disable iff (rst) ret_2 == arg_1
    );

// ret_3 is a direct copy of arg_4.
    check_ret3_passthrough: assert property (
        @(posedge clk) disable iff (rst) ret_3 == arg_4
    );

// ret_4 is a direct copy of arg_5.
    check_ret4_passthrough: assert property (
        @(posedge clk) disable iff (rst) ret_4 == arg_5
    );

// ret_5 is a direct copy of arg_6.
    check_ret5_passthrough: assert property (
        @(posedge clk) disable iff (rst) ret_5 == arg_6
    );

// ret_0 is the 21-bit sum of arg_2 and arg_3.
    check_ret0_sum: assert property (
        @(posedge clk) disable iff (rst) ret_0 == (arg_2 + arg_3)
    );

// When arg_5 and arg_6 differ, ret_0 is incremented by 1.
    check_ret0_increment_when_signs_differ: assert property (
        @(posedge clk) disable iff (rst) (arg_5 != arg_6) |-> (ret_0 == (arg_2 + arg_3 + 21'd1))
    );

// When arg_5 and arg_6 are equal, ret_0 matches the sum without increment.
    check_ret0_no_increment_when_signs_equal: assert property (
        @(posedge clk) disable iff (rst) (arg_5 == arg_6) |-> (ret_0 == (arg_2 + arg_3))
    );

endmodule
