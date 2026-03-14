module top_module_sva (
    input logic clk,              // sampling clock for assertions (RTL has no clock/reset)
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic sel1,
    input logic sel2,
    input logic [3:0] mux_out,
    input logic [3:0] comp_in1,
    input logic [3:0] comp_in2,
    input logic eq_out,
    input logic gt_out,
    input logic lt_out
);
    // Analysis: No clock/reset in RTL; pure combinational (2 always @*). MUX selects in2 only when sel1&sel2==1; else in1. Comparator directly drives eq/gt/lt.
    // Assertions below are clocked on 'clk'.

    ///// Multiplexer checks /////
    // MUX implements: mux_out = ((sel1==1)&&(sel2==1)) ? in2 : in1.
    check_mux_function: assert property (
        @(posedge clk) mux_out === (((sel1 === 1'b1) && (sel2 === 1'b1)) ? in2 : in1)
    );

    // When both selects are 1, output must be in2.
    check_mux_both_sel_to_in2: assert property (
        @(posedge clk) ((sel1 === 1'b1) && (sel2 === 1'b1)) |-> (mux_out === in2)
    );

    ///// Comparator functional mapping /////
    // eq_out matches (comp_in1 == comp_in2).
    check_comp_eq_mapping: assert property (
        @(posedge clk) eq_out === (comp_in1 == comp_in2)
    );

    // gt_out matches (comp_in1 > comp_in2).
    check_comp_gt_mapping: assert property (
        @(posedge clk) gt_out === (comp_in1 > comp_in2)
    );

    // lt_out matches (comp_in1 < comp_in2).
    check_comp_lt_mapping: assert property (
        @(posedge clk) lt_out === (comp_in1 < comp_in2)
    );

    ///// Comparator consistency /////
    // If eq_out is 1, then gt_out and lt_out must be 0.
    check_eq_excludes_gt_lt: assert property (
        @(posedge clk) (eq_out === 1'b1) |-> ((gt_out === 1'b0) && (lt_out === 1'b0))
    );

    // If gt_out is 1, then eq_out and lt_out must be 0.
    check_gt_excludes_eq_lt: assert property (
        @(posedge clk) (gt_out === 1'b1) |-> ((eq_out === 1'b0) && (lt_out === 1'b0))
    );

    // If lt_out is 1, then eq_out and gt_out must be 0.
    check_lt_excludes_eq_gt: assert property (
        @(posedge clk) (lt_out === 1'b1) |-> ((eq_out === 1'b0) && (gt_out === 1'b0))
    );

    // gt_out and lt_out cannot both be 1 simultaneously.
    check_no_gt_and_lt_same_time: assert property (
        @(posedge clk) !((gt_out === 1'b1) && (lt_out === 1'b1))
    );

    // With known comparator inputs, exactly one of {eq,gt,lt} must be 1.
    check_trichotomy_when_inputs_known: assert property (
        @(posedge clk) (!$isunknown({comp_in1, comp_in2})) |-> ((((eq_out === 1'b1) ? 1 : 0) + ((gt_out === 1'b1) ? 1 : 0) + ((lt_out === 1'b1) ? 1 : 0)) == 1)
    );
endmodule