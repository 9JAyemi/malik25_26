module mux_system_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic sel_2to1,
    input logic sel_3to1,
    input logic out,
    // Internal signals from RTL (allowed to use since present in RTL)
    input logic nand1,
    input logic nand2,
    input logic nand3,
    input logic nand4,
    input logic nand5,
    input logic nand6,
    input logic out_reg
);

    // Event for sampling combinational logic
    // (use edges of all primary inputs and output)
    // Note: No reset in RTL, so no disable iff.
    // Output equals ~c when sel_3to1 is 0.
    check_out_sel3_low: assert property (
        @(posedge a or posedge b or posedge c or posedge sel_2to1 or posedge sel_3to1 or posedge out)
        (sel_3to1 == 1'b0) |-> (out == ~c)
    );

    // Output equals ~b when sel_3to1 is 1 and sel_2to1 is 0.
    check_out_sel3_high_sel2_low: assert property (
        @(posedge a or posedge b or posedge c or posedge sel_2to1 or posedge sel_3to1 or posedge out)
        (sel_3to1 == 1'b1 && sel_2to1 == 1'b0) |-> (out == ~b)
    );

    // Output equals ~a when sel_3to1 is 1 and sel_2to1 is 1.
    check_out_sel3_high_sel2_high: assert property (
        @(posedge a or posedge b or posedge c or posedge sel_2to1 or posedge sel_3to1 or posedge out)
        (sel_3to1 == 1'b1 && sel_2to1 == 1'b1) |-> (out == ~a)
    );

    // Output equals inversion of selected input (overall function).
    check_out_overall_function: assert property (
        @(posedge a or posedge b or posedge c or posedge sel_2to1 or posedge sel_3to1 or posedge out)
        out == (sel_3to1 ? (sel_2to1 ? ~a : ~b) : ~c)
    );

    // out is driven by out_reg.
    check_out_driven_by_out_reg: assert property (
        @(posedge a or posedge b or posedge c or posedge sel_2to1 or posedge sel_3to1 or posedge out)
        out == out_reg
    );

    // nand1 implements ~(a & sel_2to1).
    check_nand1_definition: assert property (
        @(posedge a or posedge b or posedge c or posedge sel_2to1 or posedge sel_3to1 or posedge out)
        nand1 == ~(a & sel_2to1)
    );

    // nand2 implements ~(b & ~sel_2to1).
    check_nand2_definition: assert property (
        @(posedge a or posedge b or posedge c or posedge sel_2to1 or posedge sel_3to1 or posedge out)
        nand2 == ~(b & ~sel_2to1)
    );

    // nand3 implements ~(nand1 & nand2).
    check_nand3_definition: assert property (
        @(posedge a or posedge b or posedge c or posedge sel_2to1 or posedge sel_3to1 or posedge out)
        nand3 == ~(nand1 & nand2)
    );

    // nand4 implements ~(nand3 & sel_3to1).
    check_nand4_definition: assert property (
        @(posedge a or posedge b or posedge c or posedge sel_2to1 or posedge sel_3to1 or posedge out)
        nand4 == ~(nand3 & sel_3to1)
    );

    // nand5 implements ~(c & ~sel_3to1).
    check_nand5_definition: assert property (
        @(posedge a or posedge b or posedge c or posedge sel_2to1 or posedge sel_3to1 or posedge out)
        nand5 == ~(c & ~sel_3to1)
    );

    // nand6 implements ~(nand4 & nand5).
    check_nand6_definition: assert property (
        @(posedge a or posedge b or posedge c or posedge sel_2to1 or posedge sel_3to1 or posedge out)
        nand6 == ~(nand4 & nand5)
    );

    // nand3 equals 2:1 mux of a/b selected by sel_2to1.
    check_nand3_mux_ab: assert property (
        @(posedge a or posedge b or posedge c or posedge sel_2to1 or posedge sel_3to1 or posedge out)
        nand3 == (sel_2to1 ? a : b)
    );

    // out equals inversion of mux between nand3 and c selected by sel_3to1.
    check_out_mux_n3_c_inverted: assert property (
        @(posedge a or posedge b or posedge c or posedge sel_2to1 or posedge sel_3to1 or posedge out)
        out == (sel_3to1 ? ~nand3 : ~c)
    );

endmodule