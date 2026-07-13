module mux_4x1_sva (
    input logic clk,
    input logic [7:0] in0,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    input logic sel0,
    input logic sel1,
    input logic [7:0] out
);

    // sel=00 routes in0 to out.
    check_select_in0: assert property (
        @(posedge clk)
        ((sel1 == 1'b0) && (sel0 == 1'b0)) |-> (out === in0)
    );

    // sel=01 routes in1 to out.
    check_select_in1: assert property (
        @(posedge clk)
        ((sel1 == 1'b0) && (sel0 == 1'b1)) |-> (out === in1)
    );

    // sel=10 routes in2 to out.
    check_select_in2: assert property (
        @(posedge clk)
        ((sel1 == 1'b1) && (sel0 == 1'b0)) |-> (out === in2)
    );

    // sel=11 routes in3 to out.
    check_select_in3: assert property (
        @(posedge clk)
        ((sel1 == 1'b1) && (sel0 == 1'b1)) |-> (out === in3)
    );

    // If all inputs and selectors are stable, out stays stable.
    check_out_stable_when_all_inputs_stable: assert property (
        @(posedge clk)
        $stable({in0, in1, in2, in3, sel0, sel1}) |-> $stable(out)
    );

    // Unselected inputs do not affect out when select and selected input are stable.
    check_unselected_inputs_do_not_affect_out: assert property (
        @(posedge clk)
        (
            ((sel1 == 1'b0) && (sel0 == 1'b0) && $stable(sel1) && $stable(sel0) && $stable(in0)) ||
            ((sel1 == 1'b0) && (sel0 == 1'b1) && $stable(sel1) && $stable(sel0) && $stable(in1)) ||
            ((sel1 == 1'b1) && (sel0 == 1'b0) && $stable(sel1) && $stable(sel0) && $stable(in2)) ||
            ((sel1 == 1'b1) && (sel0 == 1'b1) && $stable(sel1) && $stable(sel0) && $stable(in3))
        ) |-> $stable(out)
    );

endmodule