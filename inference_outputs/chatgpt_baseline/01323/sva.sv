module Multiplexer_sva #(parameter N=1) (
    input logic              ctrl,
    input logic [N-1:0]      D0,
    input logic [N-1:0]      D1,
    input logic [N-1:0]      S
);
    // On ctrl rising, S must equal D1.
    check_ctrl_rise_selects_D1: assert property (
        @(posedge ctrl) S == D1
    );

    // On ctrl falling, S must equal D0.
    check_ctrl_fall_selects_D0: assert property (
        @(posedge (ctrl == 1'b0)) S == D0
    );

    // On any ctrl edge, S must equal the mux expression.
    check_mux_expr_on_ctrl_edge: assert property (
        @(posedge ctrl or posedge (ctrl == 1'b0)) S == (ctrl ? D1 : D0)
    );

    // When ctrl=0 and D0 has a rising bit, S must equal D0.
    check_D0_rise_when_ctrl0: assert property (
        @(posedge (|D0)) (ctrl == 1'b0) |-> (S == D0)
    );

    // When ctrl=1 and D1 has a rising bit, S must equal D1.
    check_D1_rise_when_ctrl1: assert property (
        @(posedge (|D1)) (ctrl == 1'b1) |-> (S == D1)
    );

    // If inputs are equal, S must equal that value on ctrl/data edges.
    check_equal_inputs_passthrough: assert property (
        @(posedge ctrl or posedge (ctrl == 1'b0) or posedge (|D0) or posedge (|D1))
            (D0 == D1) |-> (S == D0)
    );

    // When ctrl=0 and inputs differ, S must equal D0 on ctrl/data edges.
    check_select0_when_inputs_diff: assert property (
        @(posedge ctrl or posedge (ctrl == 1'b0) or posedge (|D0) or posedge (|D1))
            (ctrl == 1'b0 && (D0 != D1)) |-> (S == D0)
    );

    // When ctrl=1 and inputs differ, S must equal D1 on ctrl/data edges.
    check_select1_when_inputs_diff: assert property (
        @(posedge ctrl or posedge (ctrl == 1'b0) or posedge (|D0) or posedge (|D1))
            (ctrl == 1'b1 && (D0 != D1)) |-> (S == D1)
    );

    // On S rising, S must equal the mux expression.
    check_output_rise_matches_expr: assert property (
        @(posedge (|S)) S == (ctrl ? D1 : D0)
    );

    // On any data rising edge, S must equal the mux expression.
    check_mux_expr_on_data_rise: assert property (
        @(posedge (|D0) or posedge (|D1)) S == (ctrl ? D1 : D0)
    );
endmodule