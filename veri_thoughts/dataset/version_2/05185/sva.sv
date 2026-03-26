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

    // ret_1 is a direct copy of arg_0.
    check_ret1_passthrough: assert property (
        @(posedge clk) disable iff (rst)
        ret_1 == arg_0
    );

    // ret_2 is a direct copy of arg_1.
    check_ret2_passthrough: assert property (
        @(posedge clk) disable iff (rst)
        ret_2 == arg_1
    );

    // ret_3 is a direct copy of arg_4.
    check_ret3_passthrough: assert property (
        @(posedge clk) disable iff (rst)
        ret_3 == arg_4
    );

    // ret_4 is a direct copy of arg_5.
    check_ret4_passthrough: assert property (
        @(posedge clk) disable iff (rst)
        ret_4 == arg_5
    );

    // ret_5 is a direct copy of arg_6.
    check_ret5_passthrough: assert property (
        @(posedge clk) disable iff (rst)
        ret_5 == arg_6
    );

    // Equal sign bits captured this cycle select the plain sum next cycle.
    check_ret0_same_sign_next_cycle: assert property (
        @(posedge clk) disable iff (rst)
        (arg_5 == arg_6) |=> (ret_0 == ({1'b0, arg_2} + {1'b0, arg_3}))
    );

    // Different sign bits captured this cycle add one to the sum next cycle.
    check_ret0_diff_sign_next_cycle: assert property (
        @(posedge clk) disable iff (rst)
        (arg_5 != arg_6) |=> (ret_0 == ({1'b0, arg_2} + {1'b0, arg_3} + 22'd1))
    );

    // A reset cycle clears the stored sign bits, so the next cycle uses the plain sum.
    check_ret0_reset_clears_sign_state: assert property (
        @(posedge clk)
        rst |=> (ret_0 == ({1'b0, arg_2} + {1'b0, arg_3}))
    );

endmodule