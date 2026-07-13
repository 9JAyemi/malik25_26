module mux2to1_sva (
    input logic CLK,
    input logic ctrl,
    input logic D0,
    input logic D1,
    input logic S
);
    // When ctrl is 0, S must equal D0.
    check_select_ctrl0: assert property (
        @(posedge CLK) (ctrl == 1'b0) |-> (S === D0)
    );

    // When ctrl is 1, S must equal D1.
    check_select_ctrl1: assert property (
        @(posedge CLK) (ctrl == 1'b1) |-> (S === D1)
    );

    // Functional equivalence to the RTL expression.
    check_functional_equation: assert property (
        @(posedge CLK) S === ((ctrl == 1'b0) ? D0 : D1)
    );

    // If inputs are equal, S must equal that value regardless of ctrl, including X.
    check_equal_inputs_bypass_ctrl: assert property (
        @(posedge CLK) (D0 === D1) |-> (S === D0)
    );

    // If ctrl is X/Z and inputs differ, S must be unknown (X/Z).
    check_unknown_ctrl_diff_inputs_yield_unknown_S: assert property (
        @(posedge CLK) ((ctrl !== 1'b0) && (ctrl !== 1'b1) && (D0 !== D1)) |-> $isunknown(S)
    );

    // If ctrl, D0, and D1 are stable cycle-to-cycle, S must be stable.
    check_stable_inputs_keep_S_stable: assert property (
        @(posedge CLK) $stable({ctrl, D0, D1}) |-> $stable(S)
    );

    // If S changes cycle-to-cycle, at least one of ctrl/D0/D1 must have changed.
    check_S_change_requires_input_or_ctrl_change: assert property (
        @(posedge CLK) $changed(S) |-> $changed({ctrl, D0, D1})
    );
endmodule