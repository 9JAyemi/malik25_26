module sp_mux_4to1_sel2_7_1_sva (
    input logic [6:0] din1,
    input logic [6:0] din2,
    input logic [6:0] din3,
    input logic [6:0] din4,
    input logic [1:0] din5,
    input logic [6:0] dout
);

    // dout must implement the RTL's nested 4-to-1 mux function.
    check_dout_matches_mux_function: assert property (
        @($global_clock)
        dout === ((din5[1] == 1'b0) ? ((din5[0] == 1'b0) ? din1 : din2)
                                    : ((din5[0] == 1'b0) ? din3 : din4))
    );

    // Select value 00 must route din1 to dout.
    check_select_00_routes_din1: assert property (
        @($global_clock)
        (din5 == 2'b00) |-> (dout === din1)
    );

    // Select value 01 must route din2 to dout.
    check_select_01_routes_din2: assert property (
        @($global_clock)
        (din5 == 2'b01) |-> (dout === din2)
    );

    // Select value 10 must route din3 to dout.
    check_select_10_routes_din3: assert property (
        @($global_clock)
        (din5 == 2'b10) |-> (dout === din3)
    );

    // Select value 11 must route din4 to dout.
    check_select_11_routes_din4: assert property (
        @($global_clock)
        (din5 == 2'b11) |-> (dout === din4)
    );

    // With select 00 held and din1 stable, dout must stay stable.
    check_select_00_ignores_unselected_inputs: assert property (
        @($global_clock)
        ($stable(din5) && (din5 == 2'b00) && $stable(din1)) |-> $stable(dout)
    );

    // With select 01 held and din2 stable, dout must stay stable.
    check_select_01_ignores_unselected_inputs: assert property (
        @($global_clock)
        ($stable(din5) && (din5 == 2'b01) && $stable(din2)) |-> $stable(dout)
    );

    // With select 10 held and din3 stable, dout must stay stable.
    check_select_10_ignores_unselected_inputs: assert property (
        @($global_clock)
        ($stable(din5) && (din5 == 2'b10) && $stable(din3)) |-> $stable(dout)
    );

    // With select 11 held and din4 stable, dout must stay stable.
    check_select_11_ignores_unselected_inputs: assert property (
        @($global_clock)
        ($stable(din5) && (din5 == 2'b11) && $stable(din4)) |-> $stable(dout)
    );

endmodule