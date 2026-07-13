module mux_sva (
    input logic ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] S
);
    // No clock/reset in DUT; pure combinational 2:1 mux: S[0] = ctrl ? D1[0] : D0[0].
    // Sample properties on input edges (ctrl, D0[0], D1[0]).

    // On ctrl rising edge, S must equal selected input.
    check_mux_equiv_on_ctrl_posedge: assert property (
        @(posedge ctrl) S[0] == (ctrl ? D1[0] : D0[0])
    );

    // On ctrl falling edge, S must equal selected input.
    check_mux_equiv_on_ctrl_negedge: assert property (
        @(negedge ctrl) S[0] == (ctrl ? D1[0] : D0[0])
    );

    // On D0 rising edge, S must equal selected input.
    check_mux_equiv_on_d0_posedge: assert property (
        @(posedge D0[0]) S[0] == (ctrl ? D1[0] : D0[0])
    );

    // On D0 falling edge, S must equal selected input.
    check_mux_equiv_on_d0_negedge: assert property (
        @(negedge D0[0]) S[0] == (ctrl ? D1[0] : D0[0])
    );

    // On D1 rising edge, S must equal selected input.
    check_mux_equiv_on_d1_posedge: assert property (
        @(posedge D1[0]) S[0] == (ctrl ? D1[0] : D0[0])
    );

    // On D1 falling edge, S must equal selected input.
    check_mux_equiv_on_d1_negedge: assert property (
        @(negedge D1[0]) S[0] == (ctrl ? D1[0] : D0[0])
    );

    // If inputs are equal, S must equal that value regardless of ctrl (sampled on ctrl rise).
    check_equal_inputs_ctrl_posedge: assert property (
        @(posedge ctrl) (D0[0] == D1[0]) |-> (S[0] == D0[0])
    );
endmodule