module FP16RAddSubS2Of5_sva (
    input logic clk,
    input logic rst,
    input logic arg_0,
    input logic arg_1,
    input [20:0] arg_2,
    input [20:0] arg_3,
    input [4:0]  arg_4,
    input logic arg_5,
    input logic arg_6,
    output [21:0] ret_0,
    output logic ret_1,
    output logic ret_2,
    output [4:0]  ret_3,
    output logic ret_4,
    output logic ret_5
);
    // Sequential logic for xn and yn
    sequential_logic: assert property (
        @(posedge clk) disable iff (!rst) xn |-> (xn == arg_5) && (yn == arg_6)
    );

    // Combinational logic for diff_sign
    diff_sign_logic: assert property (
        @(posedge clk) disable iff (!rst) diff_sign |-> (diff_sign == (xn != yn))
    );

    // Combinational logic for rxy
    rxy_logic: assert property (
        @(posedge clk) disable iff (!rst) rxy |-> (rxy == arg_2 + arg_3)
    );

    // Combinational logic for r_final
    r_final_logic: assert property (
        @(posedge clk) disable iff (!rst) r_final |-> (r_final == (diff_sign ? (rxy + 1) : rxy))
    );

    // Combinational logic for ret_0
    ret_0_logic: assert property (
        @(posedge clk) disable iff (!rst) ret_0 |-> (ret_0 == r_final)
    );

    // Combinational logic for ret_1
    ret_1_logic: assert property (
        @(posedge clk) disable iff (!rst) ret_1 |-> (ret_1 == arg_0)
    );

    // Combinational logic for ret_2
    ret_2_logic: assert property (
        @(posedge clk) disable iff (!rst) ret_2 |-> (ret_2 == arg_1)
    );

    // Combinational logic for ret_3
    ret_3_logic: assert property (
        @(posedge clk) disable iff (!rst) ret_3 |-> (ret_3 == arg_4)
    );

    // Combinational logic for ret_4
    ret_4_logic: assert property (
        @(posedge clk) disable iff (!rst) ret_4 |-> (ret_4 == arg_5)
    );

    // Combinational logic for ret_5
    ret_5_logic: assert property (
        @(posedge clk) disable iff (!rst) ret_5 |-> (ret_5 == arg_6)
    );

    // Device reset
    reset: assert property (
        @(posedge clk) !rst |-> (xn == 0) && (yn == 0) && (diff_sign == 0) && (rxy == 0) && (r_final == 0) && (ret_0 == 0) && (ret_1 == 0) && (ret_2 == 0) && (ret_3 == 0) && (ret_4 == 0) && (ret_5 == 0)
    );
endmodule