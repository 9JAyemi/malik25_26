module Multiplexer_AC__parameterized114_sva (
    input logic ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] S
);
    // Combinational 2:1 mux; no clock/reset in RTL. Sample on signal edges to check S = ctrl ? D1 : D0.

    // On ctrl rising, S must equal D1.
    check_s_on_ctrl_high: assert property (
        @(posedge ctrl) S == D1
    );

    // On ctrl falling, S must equal D0.
    check_s_on_ctrl_low: assert property (
        @(posedge !ctrl) S == D0
    );

    // On D0 rising, S must equal the mux function.
    check_mux_on_d0_rise: assert property (
        @(posedge D0) S == (ctrl ? D1 : D0)
    );

    // On D0 falling, S must equal the mux function.
    check_mux_on_d0_fall: assert property (
        @(posedge !D0) S == (ctrl ? D1 : D0)
    );

    // On D1 rising, S must equal the mux function.
    check_mux_on_d1_rise: assert property (
        @(posedge D1) S == (ctrl ? D1 : D0)
    );

    // On D1 falling, S must equal the mux function.
    check_mux_on_d1_fall: assert property (
        @(posedge !D1) S == (ctrl ? D1 : D0)
    );

    // On S rising, S must equal the mux function.
    check_mux_on_s_rise: assert property (
        @(posedge S) S == (ctrl ? D1 : D0)
    );

    // On S falling, S must equal the mux function.
    check_mux_on_s_fall: assert property (
        @(posedge !S) S == (ctrl ? D1 : D0)
    );

    // On S rising, the selected input must be 1.
    check_s_rise_from_selected_input: assert property (
        @(posedge S) ( (ctrl && (D1 == 1'b1)) || (!ctrl && (D0 == 1'b1)) )
    );

    // On S falling, the selected input must be 0.
    check_s_fall_from_selected_input: assert property (
        @(posedge !S) ( (ctrl && (D1 == 1'b0)) || (!ctrl && (D0 == 1'b0)) )
    );

endmodule