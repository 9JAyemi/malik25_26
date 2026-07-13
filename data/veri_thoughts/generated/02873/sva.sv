module mux_3to1_enable_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] c,
    input logic       en,
    input logic [1:0] sel,
    input logic [3:0] out
);

    // Out matches the RTL's effective function (r folded into selection).
    check_function_equivalence: assert property (
        @(posedge en or posedge sel[0] or posedge sel[1] or
          posedge a[0] or posedge a[1] or posedge a[2] or posedge a[3] or
          posedge b[0] or posedge b[1] or posedge b[2] or posedge b[3] or
          posedge c[0] or posedge c[1] or posedge c[2] or posedge c[3] or
          posedge out[0] or posedge out[1] or posedge out[2] or posedge out[3])
        out == (en ? (sel[1] ? a : (sel[0] ? b : 4'b0)) : 4'b0)
    );

    // When disabled, output must be 0.
    check_out_zero_when_disabled: assert property (
        @(posedge en or posedge sel[0] or posedge sel[1] or
          posedge a[0] or posedge a[1] or posedge a[2] or posedge a[3] or
          posedge b[0] or posedge b[1] or posedge b[2] or posedge b[3] or
          posedge c[0] or posedge c[1] or posedge c[2] or posedge c[3] or
          posedge out[0] or posedge out[1] or posedge out[2] or posedge out[3])
        (!en) |-> (out == 4'b0)
    );

    // When enabled and sel[1]=1, output selects a.
    check_select_a_when_sel1: assert property (
        @(posedge en or posedge sel[0] or posedge sel[1] or
          posedge a[0] or posedge a[1] or posedge a[2] or posedge a[3] or
          posedge b[0] or posedge b[1] or posedge b[2] or posedge b[3] or
          posedge c[0] or posedge c[1] or posedge c[2] or posedge c[3] or
          posedge out[0] or posedge out[1] or posedge out[2] or posedge out[3])
        (en && sel[1]) |-> (out == a)
    );

    // When enabled and sel[1]=0, sel[0]=1, output selects b.
    check_select_b_when_sel0_only: assert property (
        @(posedge en or posedge sel[0] or posedge sel[1] or
          posedge a[0] or posedge a[1] or posedge a[2] or posedge a[3] or
          posedge b[0] or posedge b[1] or posedge b[2] or posedge b[3] or
          posedge c[0] or posedge c[1] or posedge c[2] or posedge c[3] or
          posedge out[0] or posedge out[1] or posedge out[2] or posedge out[3])
        (en && !sel[1] && sel[0]) |-> (out == b)
    );

    // When enabled and sel==2'b00, output is 0.
    check_zero_when_enabled_sel00: assert property (
        @(posedge en or posedge sel[0] or posedge sel[1] or
          posedge a[0] or posedge a[1] or posedge a[2] or posedge a[3] or
          posedge b[0] or posedge b[1] or posedge b[2] or posedge b[3] or
          posedge c[0] or posedge c[1] or posedge c[2] or posedge c[3] or
          posedge out[0] or posedge out[1] or posedge out[2] or posedge out[3])
        (en && !sel[1] && !sel[0]) |-> (out == 4'b0)
    );

    // When enabled and both sel bits are 1, a has priority over b.
    check_a_priority_when_both_sel_high: assert property (
        @(posedge en or posedge sel[0] or posedge sel[1] or
          posedge a[0] or posedge a[1] or posedge a[2] or posedge a[3] or
          posedge b[0] or posedge b[1] or posedge b[2] or posedge b[3] or
          posedge c[0] or posedge c[1] or posedge c[2] or posedge c[3] or
          posedge out[0] or posedge out[1] or posedge out[2] or posedge out[3])
        (en && sel[1] && sel[0]) |-> (out == a)
    );

endmodule