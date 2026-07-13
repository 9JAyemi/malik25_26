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

    // Reset clears the internal state and all registered outputs.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |=> (ret_4 == 1'b0 && ret_5 == 1'b0 && ret_0 == 22'd0 && ret_1 == 1'b0 && ret_2 == 1'b0 && ret_3 == 5'd0)
    );

    // ret_4 and ret_5 reflect the previous cycle's arg_5 and arg_6.
    check_registered_inputs: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (ret_4 == $past(arg_5) && ret_5 == $past(arg_6))
    );

    // ret_1 and ret_2 reflect the previous cycle's arg_0 and arg_1.
    check_registered_flags: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (ret_1 == $past(arg_0) && ret_2 == $past(arg_1))
    );

    // ret_3 reflects the previous cycle's arg_4.
    check_registered_counter: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (ret_3 == $past(arg_4))
    );

    // ret_0 is the previous cycle's arg_2 plus arg_3 with a 1-bit carry-in.
    check_sum_with_cin: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (ret_0 == ($past(arg_2) + $past(arg_3) + 22'd1))
    );

endmodule