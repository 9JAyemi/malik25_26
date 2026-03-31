module mux4to1_sva (
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic out
);

    // sel=00 routes in[0] to out.
    check_sel_00_routes_in0: assert property (
        @($global_clock) (sel == 2'b00) |-> (out == in[0])
    );

    // sel=01 routes in[1] to out.
    check_sel_01_routes_in1: assert property (
        @($global_clock) (sel == 2'b01) |-> (out == in[1])
    );

    // sel=10 routes in[2] to out.
    check_sel_10_routes_in2: assert property (
        @($global_clock) (sel == 2'b10) |-> (out == in[2])
    );

    // sel=11 routes in[3] to out.
    check_sel_11_routes_in3: assert property (
        @($global_clock) (sel == 2'b11) |-> (out == in[3])
    );

    // With sel held at 00, a change on in[0] changes out.
    check_sel_00_in0_change_updates_out: assert property (
        @($global_clock) (sel == 2'b00 && $stable(sel) && $changed(in[0])) |-> $changed(out)
    );

    // With sel held at 01, a change on in[1] changes out.
    check_sel_01_in1_change_updates_out: assert property (
        @($global_clock) (sel == 2'b01 && $stable(sel) && $changed(in[1])) |-> $changed(out)
    );

    // With sel held at 10, a change on in[2] changes out.
    check_sel_10_in2_change_updates_out: assert property (
        @($global_clock) (sel == 2'b10 && $stable(sel) && $changed(in[2])) |-> $changed(out)
    );

    // With sel held at 11, a change on in[3] changes out.
    check_sel_11_in3_change_updates_out: assert property (
        @($global_clock) (sel == 2'b11 && $stable(sel) && $changed(in[3])) |-> $changed(out)
    );

    // With sel held at 00, a change on in[1:0] does not change out.
    check_sel_00_other_in_change_no_effect: assert property (
        @($global_clock) (sel == 2'b00 && $stable(sel) && $changed(in[1:0])) |-> $stable(out)
    );

    // With sel held at 01, a change on in[2:1] does not change out.
    check_sel_01_other_in_change_no_effect: assert property (
        @($global_clock) (sel == 2'b01 && $stable(sel) && $changed(in[2:1])) |-> $stable(out)
    );

    // With sel held at 10, a change on in[3:2] does not change out.
    check_sel_10_other_in_change_no_effect: assert property (
        @($global_clock) (sel == 2'b10 && $stable(sel) && $changed(in[3:2])) |-> $stable(out)
    );

    // With sel held at 11, a change on in[3:0] does not change out.
    check_sel_11_other_in_change_no_effect: assert property (
        @($global_clock) (sel == 2'b11 && $stable(sel) && $changed(in[3:0])) |-> $stable(out)
    );

endmodule