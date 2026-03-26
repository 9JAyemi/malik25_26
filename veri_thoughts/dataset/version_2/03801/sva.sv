module mux4to1_sva (
    input logic clk,
    input logic D0,
    input logic D1,
    input logic D2,
    input logic D3,
    input logic S0,
    input logic S1,
    input logic Y
);

    // Select 00 routes D0 to Y.
    check_select_d0: assert property (
        @(posedge clk) (S1 === 1'b0 && S0 === 1'b0) |-> (Y === D0)
    );

    // Select 01 routes D1 to Y.
    check_select_d1: assert property (
        @(posedge clk) (S1 === 1'b0 && S0 === 1'b1) |-> (Y === D1)
    );

    // Select 10 routes D2 to Y.
    check_select_d2: assert property (
        @(posedge clk) (S1 === 1'b1 && S0 === 1'b0) |-> (Y === D2)
    );

    // Select 11 routes D3 to Y.
    check_select_d3: assert property (
        @(posedge clk) (S1 === 1'b1 && S0 === 1'b1) |-> (Y === D3)
    );

    // If all inputs are stable, the output must remain stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) $stable({D0, D1, D2, D3, S0, S1}) |-> $stable(Y)
    );

    // With select 00 held and D0 stable, unselected inputs must not affect Y.
    check_only_d0_matters_when_sel00: assert property (
        @(posedge clk) (S1 === 1'b0 && S0 === 1'b0 && $stable({S1, S0, D0})) |-> $stable(Y)
    );

    // With select 01 held and D1 stable, unselected inputs must not affect Y.
    check_only_d1_matters_when_sel01: assert property (
        @(posedge clk) (S1 === 1'b0 && S0 === 1'b1 && $stable({S1, S0, D1})) |-> $stable(Y)
    );

    // With select 10 held and D2 stable, unselected inputs must not affect Y.
    check_only_d2_matters_when_sel10: assert property (
        @(posedge clk) (S1 === 1'b1 && S0 === 1'b0 && $stable({S1, S0, D2})) |-> $stable(Y)
    );

    // With select 11 held and D3 stable, unselected inputs must not affect Y.
    check_only_d3_matters_when_sel11: assert property (
        @(posedge clk) (S1 === 1'b1 && S0 === 1'b1 && $stable({S1, S0, D3})) |-> $stable(Y)
    );

endmodule