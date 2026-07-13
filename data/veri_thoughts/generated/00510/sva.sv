module sp_mux_9to1_sel4_6_1_sva (
    input logic [5:0] din1,
    input logic [5:0] din2,
    input logic [5:0] din3,
    input logic [5:0] din4,
    input logic [5:0] din5,
    input logic [5:0] din6,
    input logic [5:0] din7,
    input logic [5:0] din8,
    input logic [5:0] din9,
    input logic [3:0] din10,
    input logic [5:0] dout
);

    // Full select decode must match the implemented mux function.
    check_full_mux_function: assert property (
        @($global_clock)
        dout == (din10[3] ? din9 :
                 (din10[2] ? (din10[1] ? (din10[0] ? din8 : din7)
                                       : (din10[0] ? din6 : din5))
                           : (din10[1] ? (din10[0] ? din4 : din3)
                                       : (din10[0] ? din2 : din1))))
    );

    // When the top select bit is high, dout must come from din9.
    check_sel3_selects_din9: assert property (
        @($global_clock) din10[3] |-> (dout == din9)
    );

    // Select value 0 must route din1 to dout.
    check_sel0_routes_din1: assert property (
        @($global_clock) (din10 == 4'h0) |-> (dout == din1)
    );

    // Select value 1 must route din2 to dout.
    check_sel1_routes_din2: assert property (
        @($global_clock) (din10 == 4'h1) |-> (dout == din2)
    );

    // Select value 2 must route din3 to dout.
    check_sel2_routes_din3: assert property (
        @($global_clock) (din10 == 4'h2) |-> (dout == din3)
    );

    // Select value 3 must route din4 to dout.
    check_sel3_routes_din4: assert property (
        @($global_clock) (din10 == 4'h3) |-> (dout == din4)
    );

    // Select value 4 must route din5 to dout.
    check_sel4_routes_din5: assert property (
        @($global_clock) (din10 == 4'h4) |-> (dout == din5)
    );

    // Select value 5 must route din6 to dout.
    check_sel5_routes_din6: assert property (
        @($global_clock) (din10 == 4'h5) |-> (dout == din6)
    );

    // Select value 6 must route din7 to dout.
    check_sel6_routes_din7: assert property (
        @($global_clock) (din10 == 4'h6) |-> (dout == din7)
    );

    // Select value 7 must route din8 to dout.
    check_sel7_routes_din8: assert property (
        @($global_clock) (din10 == 4'h7) |-> (dout == din8)
    );

endmodule