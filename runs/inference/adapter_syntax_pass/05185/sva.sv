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

    // ret_1 mirrors arg_0.
    check_ret1_passthrough: assert property (
        @(posedge clk) disable iff (rst)
        ret_1 == arg_0
    );

    // ret_2 mirrors arg_1.
    check_ret2_passthrough: assert property (
        @(posedge clk) disable iff (rst)
        ret_2 == arg_1
    );

    // ret_3 mirrors arg_4.
    check_ret3_passthrough: assert property (
        @(posedge clk) disable iff (rst)
        ret_3 == arg_4
    );

    // ret_4 mirrors arg_5.
    check_ret4_passthrough: assert property (
        @(posedge clk) disable iff (rst)
        ret_4 == arg_5
    );

    // ret_5 mirrors arg_6.
    check_ret5_passthrough: assert property (
        @(posedge clk) disable iff (rst)
        ret_5 == arg_6
    );

    // ret_0 is always the sum of arg_2 and arg_3.
    check_ret0_sum: assert property (
        @(posedge clk) disable iff (rst)
        ret_0 == (arg_2 + arg_3)
    );

    // ret_0 is incremented by one when arg_5 and arg_6 differ.
    check_ret0_increment_on_sign_diff: assert property (
        @(posedge clk) disable iff (rst)
        (arg_5 != arg_6) |-> (ret_0 == (arg_2 + arg_3 + 21'd1))
    );

    // ret_0 matches the full conditional sum behavior.
    check_ret0_full_function: assert property (
        @(posedge clk) disable iff (rst)
        ret_0 == ((arg_5 != arg_6) ? (arg_2 + arg_3 + 21'd1) : (arg_2 + arg_3))
    );

endmodule