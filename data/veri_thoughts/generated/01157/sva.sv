module top_module_sva (
    input logic clk,
    input logic reset,
    input logic data,
    input logic q,
    input logic [2:0] shift_reg,
    input logic [2:0] complement
);
    // functional_module out equals bitwise NOT of in1
    comb_out_is_not: assert property (
        @(posedge clk) disable iff (reset) (complement == ~shift_reg)
    );

    // shift_register shifts in previous data when prior cycle not in reset
    shiftreg_updates_from_prev: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (shift_reg == {$past(shift_reg[1:0]), $past(data)})
    );

    // d_ff captures complement[2] from the previous cycle when prior cycle not in reset
    q_captures_prev_complement_msb: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (q == $past(complement[2]))
    );

    // q equals NOT of previous shift_reg[2] when prior cycle not in reset
    q_equals_not_prev_shift2: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (q == ~ $past(shift_reg[2]))
    );

    // With 3 prior cycles out of reset, q equals NOT of data from 3 cycles ago
    q_is_not_data_3cycles_ago: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset,1) && !$past(reset,2) && !$past(reset,3)) |-> (q == ~ $past(data,3))
    );

    // With 2 prior cycles out of reset, shift_reg[2] equals data from 2 cycles ago
    shiftreg_msb_eq_data_2ago: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset,1) && !$past(reset,2)) |-> (shift_reg[2] == $past(data,2))
    );

    // On a reset cycle, shift_reg becomes 0 on the next clock
    reset_clears_shiftreg_next: assert property (
        @(posedge clk) reset |=> (shift_reg == 3'b000)
    );

    // On a reset cycle, q becomes 0 on the next clock
    reset_clears_q_next: assert property (
        @(posedge clk) reset |=> (q == 1'b0)
    );

    // While reset stays asserted, shift_reg holds 0
    shiftreg_holds_zero_during_reset: assert property (
        @(posedge clk) reset && $past(reset) |-> (shift_reg == 3'b000)
    );

    // While reset stays asserted, q holds 0
    q_holds_zero_during_reset: assert property (
        @(posedge clk) reset && $past(reset) |-> (q == 1'b0)
    );
endmodule