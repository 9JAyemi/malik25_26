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

    // With sel=00 held and in[0] stable, out remains stable.
    check_sel_00_stable_when_in0_stable: assert property (
        @($global_clock) ($stable(sel) && (sel == 2'b00) && $stable(in[0])) |-> $stable(out)
    );

    // With sel=01 held and in[1] stable, out remains stable.
    check_sel_01_stable_when_in1_stable: assert property (
        @($global_clock) ($stable(sel) && (sel == 2'b01) && $stable(in[1])) |-> $stable(out)
    );

    // With sel=10 held and in[2] stable, out remains stable.
    check_sel_10_stable_when_in2_stable: assert property (
        @($global_clock) ($stable(sel) && (sel == 2'b10) && $stable(in[2])) |-> $stable(out)
    );

    // With sel=11 held and in[3] stable, out remains stable.
    check_sel_11_stable_when_in3_stable: assert property (
        @($global_clock) ($stable(sel) && (sel == 2'b11) && $stable(in[3])) |-> $stable(out)
    );

endmodule