module Multiplexer_sva (
    input logic ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] S
);

    // When ctrl rises (becomes 1), output selects D1.
    check_ctrl_rise_selects_D1: assert property (
        @(posedge ctrl) (S == D1)
    );

    // When ctrl falls (becomes 0), output selects D0.
    check_ctrl_fall_selects_D0: assert property (
        @(negedge ctrl) (S == D0)
    );

    // On D0 rising edge, mux output matches selected input.
    check_func_on_D0_rise: assert property (
        @(posedge D0[0]) (S == (ctrl ? D1 : D0))
    );

    // On D0 falling edge, mux output matches selected input.
    check_func_on_D0_fall: assert property (
        @(negedge D0[0]) (S == (ctrl ? D1 : D0))
    );

    // On D1 rising edge, mux output matches selected input.
    check_func_on_D1_rise: assert property (
        @(posedge D1[0]) (S == (ctrl ? D1 : D0))
    );

    // On D1 falling edge, mux output matches selected input.
    check_func_on_D1_fall: assert property (
        @(negedge D1[0]) (S == (ctrl ? D1 : D0))
    );

    // On S rising edge, mux output equals selected input.
    check_func_on_S_rise: assert property (
        @(posedge S[0]) (S == (ctrl ? D1 : D0))
    );

    // On S falling edge, mux output equals selected input.
    check_func_on_S_fall: assert property (
        @(negedge S[0]) (S == (ctrl ? D1 : D0))
    );

endmodule