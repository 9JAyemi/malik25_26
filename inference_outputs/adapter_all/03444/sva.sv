module Multiplexer_AC__parameterized36_sva (
    input logic [1:0] ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] D2,
    input logic [0:0] D3,
    input logic [0:0] S
);

    // No RTL clock or reset; sample on the formal global clock.

    // ctrl=00 routes D0 to S.
    check_select_00_routes_d0: assert property (
        @($global_clock) (ctrl == 2'b00) |-> (S == D0)
    );

    // ctrl=01 routes D1 to S.
    check_select_01_routes_d1: assert property (
        @($global_clock) (ctrl == 2'b01) |-> (S == D1)
    );

    // ctrl=10 routes D2 to S.
    check_select_10_routes_d2: assert property (
        @($global_clock) (ctrl == 2'b10) |-> (S == D2)
    );

    // ctrl=11 routes D3 to S.
    check_select_11_routes_d3: assert property (
        @($global_clock) (ctrl == 2'b11) |-> (S == D3)
    );

    // With ctrl=00 held and D0 stable, S stays stable.
    check_stable_when_00_and_d0_stable: assert property (
        @($global_clock) ($stable(ctrl) && (ctrl == 2'b00) && $stable(D0)) |-> $stable(S)
    );

    // With ctrl=01 held and D1 stable, S stays stable.
    check_stable_when_01_and_d1_stable: assert property (
        @($global_clock) ($stable(ctrl) && (ctrl == 2'b01) && $stable(D1)) |-> $stable(S)
    );

    // With ctrl=10 held and D2 stable, S stays stable.
    check_stable_when_10_and_d2_stable: assert property (
        @($global_clock) ($stable(ctrl) && (ctrl == 2'b10) && $stable(D2)) |-> $stable(S)
    );

    // With ctrl=11 held and D3 stable, S stays stable.
    check_stable_when_11_and_d3_stable: assert property (
        @($global_clock) ($stable(ctrl) && (ctrl == 2'b11) && $stable(D3)) |-> $stable(S)
    );

    // With ctrl=00 held and D0 changing, S changes.
    check_change_when_00_and_d0_changes: assert property (
        @($global_clock) ($stable(ctrl) && (ctrl == 2'b00) && $changed(D0)) |-> $changed(S)
    );

    // With ctrl=01 held and D1 changing, S changes.
    check_change_when_01_and_d1_changes: assert property (
        @($global_clock) ($stable(ctrl) && (ctrl == 2'b01) && $changed(D1)) |-> $changed(S)
    );

    // With ctrl=10 held and D2 changing, S changes.
    check_change_when_10_and_d2_changes: assert property (
        @($global_clock) ($stable(ctrl) && (ctrl == 2'b10) && $changed(D2)) |-> $changed(S)
    );

    // With ctrl=11 held and D3 changing, S changes.
    check_change_when_11_and_d3_changes: assert property (
        @($global_clock) ($stable(ctrl) && (ctrl == 2'b11) && $changed(D3)) |-> $changed(S)
    );

endmodule