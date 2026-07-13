module mux2x1_sva (
    input logic [3:0] out,
    input logic sel,
    input logic [3:0] a,
    input logic [3:0] b
);
    // On sel rising edge, out must equal b.
    check_select_b_on_sel_rise: assert property (
        @(posedge sel) out == b
    );

    // On sel falling edge, out must equal a.
    check_select_a_on_sel_fall: assert property (
        @(negedge sel) out == a
    );

    // When sel==0 and any a bit changes, out reflects a.
    check_out_tracks_a_on_a_edge: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3])
        (sel == 1'b0) |-> (out == a)
    );

    // When sel==1 and any b bit changes, out reflects b.
    check_out_tracks_b_on_b_edge: assert property (
        @(posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3])
        (sel == 1'b1) |-> (out == b)
    );

    // On any relevant input change, out equals the selected input.
    check_mux_function_on_any_change: assert property (
        @(posedge sel or negedge sel or
          posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3] or
          posedge b[0] or negedge b[0] or posedge b[1] or negedge b[1] or posedge b[2] or negedge b[2] or posedge b[3] or negedge b[3])
        out == (sel ? b : a)
    );

    // Any out[0] change is due to sel toggle or the selected input bit toggling.
    check_out0_change_has_cause: assert property (
        @(posedge out[0] or negedge out[0])
        ($rose(sel) || $fell(sel) ||
         ((sel == 1'b0) && ($rose(a[0]) || $fell(a[0]))) ||
         ((sel == 1'b1) && ($rose(b[0]) || $fell(b[0]))))
    );

    // Any out[1] change is due to sel toggle or the selected input bit toggling.
    check_out1_change_has_cause: assert property (
        @(posedge out[1] or negedge out[1])
        ($rose(sel) || $fell(sel) ||
         ((sel == 1'b0) && ($rose(a[1]) || $fell(a[1]))) ||
         ((sel == 1'b1) && ($rose(b[1]) || $fell(b[1]))))
    );

    // Any out[2] change is due to sel toggle or the selected input bit toggling.
    check_out2_change_has_cause: assert property (
        @(posedge out[2] or negedge out[2])
        ($rose(sel) || $fell(sel) ||
         ((sel == 1'b0) && ($rose(a[2]) || $fell(a[2]))) ||
         ((sel == 1'b1) && ($rose(b[2]) || $fell(b[2]))))
    );

    // Any out[3] change is due to sel toggle or the selected input bit toggling.
    check_out3_change_has_cause: assert property (
        @(posedge out[3] or negedge out[3])
        ($rose(sel) || $fell(sel) ||
         ((sel == 1'b0) && ($rose(a[3]) || $fell(a[3]))) ||
         ((sel == 1'b1) && ($rose(b[3]) || $fell(b[3]))))
    );
endmodule