module Multiplexer_sva #(parameter WIDTH = 1) (
    input logic ctrl,
    input logic [WIDTH-1:0] D0,
    input logic [WIDTH-1:0] D1,
    input logic [WIDTH-1:0] S
);
    // When ctrl==0, S equals D0.
    select_d0_when_ctrl0: assert property (
        @($global_clock) (ctrl == 1'b0) |-> (S == D0)
    );

    // When ctrl==1, S equals D1.
    select_d1_when_ctrl1: assert property (
        @($global_clock) (ctrl == 1'b1) |-> (S == D1)
    );

    // S implements the mux function S = ctrl ? D1 : D0.
    mux_function_definition: assert property (
        @($global_clock) (S == ((ctrl == 1'b0) ? D0 : D1))
    );

    // If inputs are equal, S must equal that value.
    equal_inputs_tieoff: assert property (
        @($global_clock) (D0 == D1) |-> (S == D0)
    );

    // If ctrl, D0, and D1 are stable, S must be stable.
    output_stable_when_all_static: assert property (
        @($global_clock) ($stable(ctrl) && $stable(D0) && $stable(D1)) |-> $stable(S)
    );

    // On ctrl rising edge, S equals D1.
    output_matches_d1_on_ctrl_rise: assert property (
        @($global_clock) $rose(ctrl) |-> (S == D1)
    );

    // On ctrl falling edge, S equals D0.
    output_matches_d0_on_ctrl_fall: assert property (
        @($global_clock) $fell(ctrl) |-> (S == D0)
    );

    // With ctrl held at 0 and D0 stable, S must be stable.
    stable_out_when_select0_and_d0_stable: assert property (
        @($global_clock) (ctrl == 1'b0 && $stable(ctrl) && $stable(D0)) |-> $stable(S)
    );

    // With ctrl held at 1 and D1 stable, S must be stable.
    stable_out_when_select1_and_d1_stable: assert property (
        @($global_clock) (ctrl == 1'b1 && $stable(ctrl) && $stable(D1)) |-> $stable(S)
    );

    // With ctrl held at 0, S changes iff D0 changes.
    change_correlation_ctrl0: assert property (
        @($global_clock) ($stable(ctrl) && (ctrl == 1'b0)) |-> ($changed(S) == $changed(D0))
    );

    // With ctrl held at 1, S changes iff D1 changes.
    change_correlation_ctrl1: assert property (
        @($global_clock) ($stable(ctrl) && (ctrl == 1'b1)) |-> ($changed(S) == $changed(D1))
    );

    // If ctrl toggles while D0==D1, S must not change.
    ctrl_toggle_no_effect_when_inputs_equal: assert property (
        @($global_clock) ($changed(ctrl) && (D0 == D1)) |-> $stable(S)
    );
endmodule