module parameterized_mux_sva #(parameter DATA_WIDTH = 1) (
    input logic clk,
    input logic ctrl,
    input logic [DATA_WIDTH-1:0] D0,
    input logic [DATA_WIDTH-1:0] D1,
    input logic [DATA_WIDTH-1:0] S
);

    // S always matches the mux select expression.
    check_mux_function: assert property (
        @(posedge clk) S === (ctrl ? D1 : D0)
    );

    // When ctrl is low, S selects D0.
    check_select_d0: assert property (
        @(posedge clk) !ctrl |-> (S === D0)
    );

    // When ctrl is high, S selects D1.
    check_select_d1: assert property (
        @(posedge clk) ctrl |-> (S === D1)
    );

    // If all inputs are stable, S remains stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({ctrl, D0, D1}) |-> $stable(S)
    );

    // When D0 is selected, changes on D1 alone do not affect S.
    check_d1_unselected_no_effect: assert property (
        @(posedge clk) !ctrl && $stable({ctrl, D0}) && $changed(D1) |-> $stable(S)
    );

    // When D1 is selected, changes on D0 alone do not affect S.
    check_d0_unselected_no_effect: assert property (
        @(posedge clk) ctrl && $stable({ctrl, D1}) && $changed(D0) |-> $stable(S)
    );

endmodule