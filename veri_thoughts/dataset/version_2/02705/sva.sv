module Multiplexer_AC__parameterized9_sva (
    input logic ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] S
);
    // On ctrl rising, output selects D1.
    check_sel1_on_ctrl_rise: assert property (
        @(posedge ctrl) S == D1
    );

    // On ctrl falling, output selects D0.
    check_sel0_on_ctrl_fall: assert property (
        @(negedge ctrl) S == D0
    );

    // When D0 rises and ctrl selects 0, S equals D0.
    follow_d0_on_rise_when_sel0: assert property (
        @(posedge D0[0]) (ctrl === 1'b0) |-> (S == D0)
    );

    // When D0 falls and ctrl selects 0, S equals D0.
    follow_d0_on_fall_when_sel0: assert property (
        @(negedge D0[0]) (ctrl === 1'b0) |-> (S == D0)
    );

    // When D1 rises and ctrl selects 1, S equals D1.
    follow_d1_on_rise_when_sel1: assert property (
        @(posedge D1[0]) (ctrl === 1'b1) |-> (S == D1)
    );

    // When D1 falls and ctrl selects 1, S equals D1.
    follow_d1_on_fall_when_sel1: assert property (
        @(negedge D1[0]) (ctrl === 1'b1) |-> (S == D1)
    );

    // If ctrl is 0 (known), S equals D0 on any relevant edge.
    ctrl0_implies_out_eq_d0: assert property (
        @(posedge ctrl or negedge ctrl or posedge D0[0] or negedge D0[0] or posedge D1[0] or negedge D1[0] or posedge S[0] or negedge S[0])
            (ctrl === 1'b0) |-> (S == D0)
    );

    // If ctrl is 1 (known), S equals D1 on any relevant edge.
    ctrl1_implies_out_eq_d1: assert property (
        @(posedge ctrl or negedge ctrl or posedge D0[0] or negedge D0[0] or posedge D1[0] or negedge D1[0] or posedge S[0] or negedge S[0])
            (ctrl === 1'b1) |-> (S == D1)
    );

    // Output equals the mux equation at edges of inputs or output.
    check_mux_equation_on_any_edge: assert property (
        @(posedge ctrl or negedge ctrl or posedge D0[0] or negedge D0[0] or posedge D1[0] or negedge D1[0] or posedge S[0] or negedge S[0])
            (S == ((ctrl == 1'b0) ? D0 : D1))
    );

    // When inputs are equal, toggling ctrl still yields that value.
    equal_inputs_ctrl_edge_value: assert property (
        @(posedge ctrl or negedge ctrl) (D0 == D1) |-> (S == D0)
    );
endmodule