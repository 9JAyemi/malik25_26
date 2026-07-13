module Ramifier_sva #(
    parameter BRANCH_CONDITION_WIDTH = 4
)(
    input logic clk,
    input logic [(BRANCH_CONDITION_WIDTH - 1):0] condition,
    input logic negative_flag,
    input logic zero_flag,
    input logic carry_flag,
    input logic overflow_flag,
    input logic take
);
    // When condition==0, take equals zero_flag.
    check_take_cond0_zero: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd0) |-> (take === zero_flag)
    );
    // When condition==1, take equals !zero_flag.
    check_take_cond1_not_zero: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd1) |-> (take === !zero_flag)
    );
    // When condition==2, take equals carry_flag.
    check_take_cond2_carry: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd2) |-> (take === carry_flag)
    );
    // When condition==3, take equals !carry_flag.
    check_take_cond3_not_carry: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd3) |-> (take === !carry_flag)
    );
    // When condition==4, take equals negative_flag.
    check_take_cond4_negative: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd4) |-> (take === negative_flag)
    );
    // When condition==5, take equals !negative_flag.
    check_take_cond5_not_negative: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd5) |-> (take === !negative_flag)
    );
    // When condition==6, take equals overflow_flag.
    check_take_cond6_overflow: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd6) |-> (take === overflow_flag)
    );
    // When condition==7, take equals !overflow_flag.
    check_take_cond7_not_overflow: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd7) |-> (take === !overflow_flag)
    );
    // When condition==8, take equals carry_flag && !zero_flag.
    check_take_cond8_carry_and_not_zero: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd8) |-> (take === (carry_flag && !zero_flag))
    );
    // When condition==9, take equals !carry_flag || zero_flag.
    check_take_cond9_notcarry_or_zero: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd9) |-> (take === (!carry_flag || zero_flag))
    );
    // When condition==10, take equals negative_flag XNOR overflow_flag.
    check_take_cond10_neg_xnor_ovf: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd10) |-> (take === (negative_flag ^~ overflow_flag))
    );
    // When condition==11, take equals negative_flag XOR overflow_flag.
    check_take_cond11_neg_xor_ovf: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd11) |-> (take === (negative_flag ^ overflow_flag))
    );
    // When condition==12, take equals !zero_flag && (negative_flag XNOR overflow_flag).
    check_take_cond12_notzero_and_xnor: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd12) |-> (take === (!zero_flag && (negative_flag ^~ overflow_flag)))
    );
    // When condition==13, take equals zero_flag || (negative_flag XOR overflow_flag).
    check_take_cond13_zero_or_xor: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd13) |-> (take === (zero_flag || (negative_flag ^ overflow_flag)))
    );
    // When condition==14, take must be 1.
    check_take_cond14_one: assert property (
        @(posedge clk) disable iff (1'b0) (condition == 'd14) |-> (take === 1'b1)
    );
    // For any other condition, take must be 0 (default case).
    check_take_default_zero: assert property (
        @(posedge clk) disable iff (1'b0) (!(condition inside { 'd0, 'd1, 'd2, 'd3, 'd4, 'd5, 'd6, 'd7, 'd8, 'd9, 'd10, 'd11, 'd12, 'd13, 'd14 })) |-> (take === 1'b0)
    );
endmodule