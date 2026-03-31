module mux_sva (
    input logic [3:0] ABCD,
    input logic [1:0] SEL,
    input logic EN,
    input logic Y
);

    // When disabled, Y must be low.
    check_disabled_forces_low: assert property (
        @($global_clock) (EN == 1'b0) |-> (Y == 1'b0)
    );

    // When enabled and SEL is 00, Y must match ABCD[0].
    check_sel_00_routes_abcd0: assert property (
        @($global_clock) (EN == 1'b1 && SEL == 2'b00) |-> (Y == ABCD[0])
    );

    // When enabled and SEL is 01, Y must match ABCD[1].
    check_sel_01_routes_abcd1: assert property (
        @($global_clock) (EN == 1'b1 && SEL == 2'b01) |-> (Y == ABCD[1])
    );

    // When enabled and SEL is 10, Y must match ABCD[2].
    check_sel_10_routes_abcd2: assert property (
        @($global_clock) (EN == 1'b1 && SEL == 2'b10) |-> (Y == ABCD[2])
    );

    // When enabled and SEL is 11, Y must match ABCD[3].
    check_sel_11_routes_abcd3: assert property (
        @($global_clock) (EN == 1'b1 && SEL == 2'b11) |-> (Y == ABCD[3])
    );

endmodule