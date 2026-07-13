module four_to_one_mux_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic [1:0] sel,
    input logic out
);
    // Out equals in0 when sel==00.
    check_mux_sel_00: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == in0)
    );

    // Out equals in1 when sel==01.
    check_mux_sel_01: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == in1)
    );

    // Out equals in2 when sel==10.
    check_mux_sel_10: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == in2)
    );

    // Out equals in3 when sel==11.
    check_mux_sel_11: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == in3)
    );

    // If sel==00 and sel/in0 are stable over the cycle, out is stable.
    check_stable_out_sel00: assert property (
        @(posedge clk) ($stable(sel) && (sel == 2'b00) && $stable(in0)) |-> $stable(out)
    );

    // If sel==01 and sel/in1 are stable over the cycle, out is stable.
    check_stable_out_sel01: assert property (
        @(posedge clk) ($stable(sel) && (sel == 2'b01) && $stable(in1)) |-> $stable(out)
    );

    // If sel==10 and sel/in2 are stable over the cycle, out is stable.
    check_stable_out_sel10: assert property (
        @(posedge clk) ($stable(sel) && (sel == 2'b10) && $stable(in2)) |-> $stable(out)
    );

    // If sel==11 and sel/in3 are stable over the cycle, out is stable.
    check_stable_out_sel11: assert property (
        @(posedge clk) ($stable(sel) && (sel == 2'b11) && $stable(in3)) |-> $stable(out)
    );
endmodule