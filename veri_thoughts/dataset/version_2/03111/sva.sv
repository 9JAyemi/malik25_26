module jt12_sh24_assertions #(parameter width=5) (
    input logic clk,
    input logic clk_en,
    input logic [width-1:0] din,
    input logic [width-1:0] st1,
    input logic [width-1:0] st2,
    input logic [width-1:0] st3,
    input logic [width-1:0] st4,
    input logic [width-1:0] st5,
    input logic [width-1:0] st6,
    input logic [width-1:0] st7,
    input logic [width-1:0] st8,
    input logic [width-1:0] st9,
    input logic [width-1:0] st10,
    input logic [width-1:0] st11,
    input logic [width-1:0] st12,
    input logic [width-1:0] st13,
    input logic [width-1:0] st14,
    input logic [width-1:0] st15,
    input logic [width-1:0] st16,
    input logic [width-1:0] st17,
    input logic [width-1:0] st18,
    input logic [width-1:0] st19,
    input logic [width-1:0] st20,
    input logic [width-1:0] st21,
    input logic [width-1:0] st22,
    input logic [width-1:0] st23,
    input logic [width-1:0] st24
);

    // When enabled, din loads into st1 and stages 2-4 shift forward.
    check_shift_stage_1_to_4: assert property (
        @(posedge clk)
        clk_en |=> (st1 == $past(din) &&
                    st2 == $past(st1) &&
                    st3 == $past(st2) &&
                    st4 == $past(st3))
    );

    // When enabled, stages 5-8 shift forward.
    check_shift_stage_5_to_8: assert property (
        @(posedge clk)
        clk_en |=> (st5 == $past(st4) &&
                    st6 == $past(st5) &&
                    st7 == $past(st6) &&
                    st8 == $past(st7))
    );

    // When enabled, stages 9-12 shift forward.
    check_shift_stage_9_to_12: assert property (
        @(posedge clk)
        clk_en |=> (st9  == $past(st8)  &&
                    st10 == $past(st9)  &&
                    st11 == $past(st10) &&
                    st12 == $past(st11))
    );

    // When enabled, stages 13-16 shift forward.
    check_shift_stage_13_to_16: assert property (
        @(posedge clk)
        clk_en |=> (st13 == $past(st12) &&
                    st14 == $past(st13) &&
                    st15 == $past(st14) &&
                    st16 == $past(st15))
    );

    // When enabled, stages 17-20 shift forward.
    check_shift_stage_17_to_20: assert property (
        @(posedge clk)
        clk_en |=> (st17 == $past(st16) &&
                    st18 == $past(st17) &&
                    st19 == $past(st18) &&
                    st20 == $past(st19))
    );

    // When enabled, stages 21-24 shift forward.
    check_shift_stage_21_to_24: assert property (
        @(posedge clk)
        clk_en |=> (st21 == $past(st20) &&
                    st22 == $past(st21) &&
                    st23 == $past(st22) &&
                    st24 == $past(st23))
    );

    // When disabled, stages 1-4 hold their values.
    check_hold_stage_1_to_4: assert property (
        @(posedge clk)
        !clk_en |=> (st1 == $past(st1) &&
                     st2 == $past(st2) &&
                     st3 == $past(st3) &&
                     st4 == $past(st4))
    );

    // When disabled, stages 5-8 hold their values.
    check_hold_stage_5_to_8: assert property (
        @(posedge clk)
        !clk_en |=> (st5 == $past(st5) &&
                     st6 == $past(st6) &&
                     st7 == $past(st7) &&
                     st8 == $past(st8))
    );

    // When disabled, stages 9-12 hold their values.
    check_hold_stage_9_to_12: assert property (
        @(posedge clk)
        !clk_en |=> (st9  == $past(st9)  &&
                     st10 == $past(st10) &&
                     st11 == $past(st11) &&
                     st12 == $past(st12))
    );

    // When disabled, stages 13-16 hold their values.
    check_hold_stage_13_to_16: assert property (
        @(posedge clk)
        !clk_en |=> (st13 == $past(st13) &&
                     st14 == $past(st14) &&
                     st15 == $past(st15) &&
                     st16 == $past(st16))
    );

    // When disabled, stages 17-20 hold their values.
    check_hold_stage_17_to_20: assert property (
        @(posedge clk)
        !clk_en |=> (st17 == $past(st17) &&
                     st18 == $past(st18) &&
                     st19 == $past(st19) &&
                     st20 == $past(st20))
    );

    // When disabled, stages 21-24 hold their values.
    check_hold_stage_21_to_24: assert property (
        @(posedge clk)
        !clk_en |=> (st21 == $past(st21) &&
                     st22 == $past(st22) &&
                     st23 == $past(st23) &&
                     st24 == $past(st24))
    );

    sequence enabled_24_cycles;
        clk_en[*24];
    endsequence

    // After 24 consecutive enabled cycles, st24 reflects din from 24 cycles earlier.
    check_end_to_end_24_cycle_shift: assert property (
        @(posedge clk)
        enabled_24_cycles |=> (st24 == $past(din, 24))
    );

endmodule