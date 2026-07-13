module oh_mux4_sva #(parameter DW = 1) (
    input logic        sel3,
    input logic        sel2,
    input logic        sel1,
    input logic        sel0,
    input logic [DW-1:0] in3,
    input logic [DW-1:0] in2,
    input logic [DW-1:0] in1,
    input logic [DW-1:0] in0,
    input logic [DW-1:0] out
);

    // Output matches the implemented 4-to-1 mux equation.
    check_mux_equation: assert property (
        @($global_clock)
        out == (({DW{sel0}} & in0) |
                ({DW{sel1}} & in1) |
                ({DW{sel2}} & in2) |
                ({DW{sel3}} & in3))
    );

    // When sel0 is high, out selects in0.
    check_sel0_selects_in0: assert property (
        @($global_clock)
        sel0 |-> (out == in0)
    );

    // When sel1 is high, out selects in1.
    check_sel1_selects_in1: assert property (
        @($global_clock)
        sel1 |-> (out == in1)
    );

    // When sel2 is high, out selects in2.
    check_sel2_selects_in2: assert property (
        @($global_clock)
        sel2 |-> (out == in2)
    );

    // When sel3 is high, out selects in3.
    check_sel3_selects_in3: assert property (
        @($global_clock)
        sel3 |-> (out == in3)
    );

    // With no select asserted, out is zero.
    check_no_selects_drive_zero: assert property (
        @($global_clock)
        !(sel0 || sel1 || sel2 || sel3) |-> (out == '0)
    );

    // With exactly one select asserted, out matches the selected input.
    check_onehot_selects_drive_selected_input: assert property (
        @($global_clock)
        $onehot({sel3, sel2, sel1, sel0}) |-> (out == ($onehot_sel({sel3, sel2, sel1, sel0}) ? in3 : in2) ||
                                                ($onehot_sel({sel3, sel2, sel1, sel0}) ? in2 : in1) ||
                                                ($onehot_sel({sel3, sel2, sel1, sel0}) ? in1 : in0))
    );

    // With exactly two selects asserted, out is the OR of the two selected inputs.
    check_twohot_selects_drive_or_of_selected_inputs: assert property (
        @($global_clock)
        $onehot0({sel3, sel2, sel1, sel0}) |-> (out == ((sel0 & sel1) ? (in0 | in1) :
                                                         (sel0 & sel2) ? (in0 | in2) :
                                                         (sel0 & sel3) ? (in0 | in3) :
                                                         (sel1 & sel2) ? (in1 | in2) :
                                                         (sel1 & sel3) ? (in1 | in3) :
                                                         (sel2 & sel3) ? (in2 | in3) : '0))
    );

    // With exactly three selects asserted, out is the OR of all three selected inputs.
    check_threehot_selects_drive_or_of_selected_inputs: assert property (
        @($global_clock)
        $onehot0({~sel3, ~sel2, ~sel1, ~sel0}) |-> (out == ((sel0 & sel1 & sel2) ? (in0 | in1 | in2) :
                                                            (sel0 & sel1 & sel3) ? (in0 | in1 | in3) :
                                                            (sel0 & sel2 & sel3) ? (in0 | in2 | in3) :
                                                            (sel1 & sel2 & sel3) ? (in1 | in2 | in3) : '0))
    );

    // With all selects asserted, out is the OR of all four inputs.
    check_all_selects_drive_or_of_all_inputs: assert property (
        @($global_clock)
        (sel0 && sel1 && sel2 && sel3) |-> (out == (in0 | in1 | in2 | in3))
    );

endmodule