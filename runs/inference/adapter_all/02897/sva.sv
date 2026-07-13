module mux4_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic       sel0,
    input logic       sel1,
    input logic [3:0] out
);

    // No RTL clock or reset; sample combinational behavior on the global clock.

    // sel1=0 and sel0=0 select in0.
    check_sel00_selects_in0: assert property (
        @($global_clock) (!sel1 && !sel0) |-> (out == in0)
    );

    // sel1=0 and sel0=1 select in1.
    check_sel01_selects_in1: assert property (
        @($global_clock) (!sel1 && sel0) |-> (out == in1)
    );

    // sel1=1 and sel0=0 select in2.
    check_sel10_selects_in2: assert property (
        @($global_clock) (sel1 && !sel0) |-> (out == in2)
    );

    // sel1=1 and sel0=1 select in3.
    check_sel11_selects_in3: assert property (
        @($global_clock) (sel1 && sel0) |-> (out == in3)
    );

    // With sel1=0 held low, a rising sel0 selects in1.
    check_sel1_rise_selects_in1: assert property (
        @($global_clock) (!$past(sel1) && sel1 && !sel0) |-> (out == in1)
    );

    // With sel1=0 held low, a falling sel0 selects in0.
    check_sel0_fall_selects_in0: assert property (
        @($global_clock) ($past(sel1) && !sel1 && !sel0) |-> (out == in0)
    );

    // With sel1=1 held high, a rising sel0 selects in3.
    check_sel1_rise_selects_in3: assert property (
        @($global_clock) (!$past(sel1) && sel1 && sel0) |-> (out == in3)
    );

    // With sel1=1 held high, a falling sel0 selects in2.
    check_sel0_fall_selects_in2: assert property (
        @($global_clock) ($past(sel1) && sel1 && !sel0) |-> (out == in2)
    );

    // With sel0=0 held low, a rising sel1 selects in2.
    check_sel0_rise_selects_in2: assert property (
        @($global_clock) (!$past(sel0) && !sel0 && sel1) |-> (out == in2)
    );

    // With sel0=0 held low, a falling sel1 selects in0.
    check_sel1_fall_selects_in0: assert property (
        @($global_clock) ($past(sel0) && !sel0 && !sel1) |-> (out == in0)
    );

    // With sel0=1 held high, a rising sel1 selects in3.
    check_sel0_rise_selects_in3: assert property (
        @($global_clock) (!$past(sel0) && sel0 && sel1) |-> (out == in3)
    );

    // With sel0=1 held high, a falling sel1 selects in1.
    check_sel1_fall_selects_in1: assert property (
        @($global_clock) ($past(sel0) && sel0 && !sel1) |-> (out == in1)
    );

endmodule