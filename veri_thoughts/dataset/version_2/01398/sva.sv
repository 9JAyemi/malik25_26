module mux2to1_case_sva (
    input logic in1,
    input logic in2,
    input logic sel,
    input logic out
);
    // Out equals selected input on any input edge.
    check_mux_function: assert property (
        @(posedge sel or negedge sel or posedge in1 or negedge in1 or posedge in2 or negedge in2)
            out == (sel ? in2 : in1)
    );

    // Out equals in2 on sel rising edge.
    check_sel1_path: assert property (
        @(posedge sel) out == in2
    );

    // Out equals in1 on sel falling edge.
    check_sel0_path: assert property (
        @(negedge sel) out == in1
    );

    // Unselected input in2 has no effect when sel=0 and in1/sel are stable.
    check_unselected_in2_no_effect_when_sel0: assert property (
        @(posedge in2 or negedge in2)
            (sel == 1'b0 && $stable(in1) && $stable(sel)) |-> $stable(out)
    );

    // Unselected input in1 has no effect when sel=1 and in2/sel are stable.
    check_unselected_in1_no_effect_when_sel1: assert property (
        @(posedge in1 or negedge in1)
            (sel == 1'b1 && $stable(in2) && $stable(sel)) |-> $stable(out)
    );

    // Any out change is explained by a sel change or a change on the selected input.
    check_out_change_has_cause: assert property (
        @(posedge out or negedge out)
            (!$stable(sel)) || ((sel == 1'b0) && (!$stable(in1))) || ((sel == 1'b1) && (!$stable(in2)))
    );
endmodule