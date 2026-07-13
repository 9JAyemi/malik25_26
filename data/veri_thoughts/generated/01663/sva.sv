module mux2to1_sva (
    input logic CLK,
    input logic o,
    input logic a,
    input logic b,
    input logic sel
);
    // o equals selected input each cycle.
    check_mux_function: assert property (
        @(posedge CLK) o == (sel ? b : a)
    );

    // When sel=0, output equals a.
    check_sel0_path: assert property (
        @(posedge CLK) (sel == 1'b0) |-> (o == a)
    );

    // When sel=1, output equals b.
    check_sel1_path: assert property (
        @(posedge CLK) (sel == 1'b1) |-> (o == b)
    );

    // On sel rising edge, output selects b.
    check_output_on_sel_rise: assert property (
        @(posedge CLK) $rose(sel) |-> (o == b)
    );

    // On sel falling edge, output selects a.
    check_output_on_sel_fall: assert property (
        @(posedge CLK) $fell(sel) |-> (o == a)
    );

    // If a changes while sel=0, output equals a.
    check_follow_a_when_sel0: assert property (
        @(posedge CLK) $changed(a) && (sel == 1'b0) |-> (o == a)
    );

    // If b changes while sel=1, output equals b.
    check_follow_b_when_sel1: assert property (
        @(posedge CLK) $changed(b) && (sel == 1'b1) |-> (o == b)
    );

    // If inputs unchanged from last cycle, output unchanged.
    check_output_stable_with_inputs: assert property (
        @(posedge CLK) ((a == $past(a)) && (b == $past(b)) && (sel == $past(sel))) |-> (o == $past(o))
    );

    // If a==b, output equals that common value.
    check_equal_inputs_passthrough: assert property (
        @(posedge CLK) (a == b) |-> (o == a)
    );
endmodule