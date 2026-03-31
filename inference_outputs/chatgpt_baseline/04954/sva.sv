module pipelined_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] OUT,
    input logic [3:0] sum_reg1,
    input logic [3:0] sum_reg2,
    input logic [3:0] sum_reg3
);

    // OUT is the current value of the third pipeline stage.
    check_out_matches_sum_reg3: assert property (
        @(posedge clk)
        !$isunknown({OUT, sum_reg3}) |-> (OUT == sum_reg3)
    );

    // The first stage holds the previous cycle's sum of A and B.
    check_sum_reg1_captures_input_sum: assert property (
        @(posedge clk)
        (!$isunknown($past(A)) && !$isunknown($past(B)))
        |-> (sum_reg1 == ($past(A) + $past(B)))
    );

    // The second stage holds the previous cycle's first-stage value.
    check_sum_reg2_follows_sum_reg1: assert property (
        @(posedge clk)
        !$isunknown($past(sum_reg1))
        |-> (sum_reg2 == $past(sum_reg1))
    );

    // The third stage holds the previous cycle's second-stage value.
    check_sum_reg3_follows_sum_reg2: assert property (
        @(posedge clk)
        !$isunknown($past(sum_reg2))
        |-> (sum_reg3 == $past(sum_reg2))
    );

    // The second stage matches the input sum from two cycles earlier.
    check_sum_reg2_matches_two_cycle_old_sum: assert property (
        @(posedge clk)
        (!$isunknown($past(A, 2)) && !$isunknown($past(B, 2)))
        |-> (sum_reg2 == ($past(A, 2) + $past(B, 2)))
    );

    // The third stage matches the input sum from three cycles earlier.
    check_sum_reg3_matches_three_cycle_old_sum: assert property (
        @(posedge clk)
        (!$isunknown($past(A, 3)) && !$isunknown($past(B, 3)))
        |-> (sum_reg3 == ($past(A, 3) + $past(B, 3)))
    );

    // OUT reflects the input sum from three cycles earlier.
    check_out_matches_three_cycle_old_sum: assert property (
        @(posedge clk)
        (!$isunknown($past(A, 3)) && !$isunknown($past(B, 3)) && !$isunknown(OUT))
        |-> (OUT == ($past(A, 3) + $past(B, 3)))
    );

endmodule