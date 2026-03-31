module four_to_one_mux_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic [1:0] sel,
    input logic out
);

    // sel=00 routes in0 to out.
    check_sel_00_routes_in0: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == in0)
    );

    // sel=01 routes in1 to out.
    check_sel_01_routes_in1: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == in1)
    );

    // sel=10 routes in2 to out.
    check_sel_10_routes_in2: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == in2)
    );

    // sel=11 routes in3 to out.
    check_sel_11_routes_in3: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == in3)
    );

    // With sel held at 00, a change on in0 changes out.
    check_sel_00_in0_change_updates_out: assert property (
        @(posedge clk) (sel == 2'b00 && $stable(sel) && $changed(in0)) |-> $changed(out)
    );

    // With sel held at 01, a change on in1 changes out.
    check_sel_01_in1_change_updates_out: assert property (
        @(posedge clk) (sel == 2'b01 && $stable(sel) && $changed(in1)) |-> $changed(out)
    );

    // With sel held at 10, a change on in2 changes out.
    check_sel_10_in2_change_updates_out: assert property (
        @(posedge clk) (sel == 2'b10 && $stable(sel) && $changed(in2)) |-> $changed(out)
    );

    // With sel held at 11, a change on in3 changes out.
    check_sel_11_in3_change_updates_out: assert property (
        @(posedge clk) (sel == 2'b11 && $stable(sel) && $changed(in3)) |-> $changed(out)
    );

    // With sel held at 00, a change on in1 does not change out.
    check_sel_00_in1_change_ignored: assert property (
        @(posedge clk) (sel == 2'b00 && $stable(sel) && $changed(in1)) |-> !$changed(out)
    );

    // With sel held at 00, a change on in2 does not change out.
    check_sel_00_in2_change_ignored: assert property (
        @(posedge clk) (sel == 2'b00 && $stable(sel) && $changed(in2)) |-> !$changed(out)
    );

    // With sel held at 00, a change on in3 does not change out.
    check_sel_00_in3_change_ignored: assert property (
        @(posedge clk) (sel == 2'b00 && $stable(sel) && $changed(in3)) |-> !$changed(out)
    );

    // With sel held at 01, a change on in0 does not change out.
    check_sel_01_in0_change_ignored: assert property (
        @(posedge clk) (sel == 2'b01 && $stable(sel) && $changed(in0)) |-> !$changed(out)
    );

    // With sel held at 01, a change on in2 does not change out.
    check_sel_01_in2_change_ignored: assert property (
        @(posedge clk) (sel == 2'b01 && $stable(sel) && $changed(in2)) |-> !$changed(out)
    );

    // With sel held at 01, a change on in3 does not change out.
    check_sel_01_in3_change_ignored: assert property (
        @(posedge clk) (sel == 2'b01 && $stable(sel) && $changed(in3)) |-> !$changed(out)
    );

    // With sel held at 10, a change on in0 does not change out.
    check_sel_10_in0_change_ignored: assert property (
        @(posedge clk) (sel == 2'b10 && $stable(sel) && $changed(in0)) |-> !$changed(out)
    );

    // With sel held at 10, a change on in1 does not change out.
    check_sel_10_in1_change_ignored: assert property (
        @(posedge clk) (sel == 2'b10 && $stable(sel) && $changed(in1)) |-> !$changed(out)
    );

    // With sel held at 10, a change on in3 does not change out.
    check_sel_10_in3_change_ignored: assert property (
        @(posedge clk) (sel == 2'b10 && $stable(sel) && $changed(in3)) |-> !$changed(out)
    );

    // With sel held at 11, a change on in0 does not change out.
    check_sel_11_in0_change_ignored: assert property (
        @(posedge clk) (sel == 2'b11 && $stable(sel) && $changed(in0)) |-> !$changed(out)
    );

    // With sel held at 11, a change on in1 does not change out.
    check_sel_11_in1_change_ignored: assert property (
        @(posedge clk) (sel == 2'b11 && $stable(sel) && $changed(in1)) |-> !$changed(out)
    );

    // With sel held at 11, a change on in2 does not change out.
    check_sel_11_in2_change_ignored: assert property (
        @(posedge clk) (sel == 2'b11 && $stable(sel) && $changed(in2)) |-> !$changed(out)
    );

endmodule