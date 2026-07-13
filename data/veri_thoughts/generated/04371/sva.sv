module mux4_2_assertions (
    input logic clk,
    input logic X,
    input logic A0,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic S0,
    input logic S1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // RTL is combinational; clk is an external sampling clock and there is no reset.
    // S1:S0 selects A0-A3 onto X.

    // S=00 routes A0 to X.
    check_select_00_routes_a0: assert property (
        @(posedge clk) ((S1 === 1'b0) && (S0 === 1'b0)) |-> (X === A0)
    );

    // S=01 routes A1 to X.
    check_select_01_routes_a1: assert property (
        @(posedge clk) ((S1 === 1'b0) && (S0 === 1'b1)) |-> (X === A1)
    );

    // S=10 routes A2 to X.
    check_select_10_routes_a2: assert property (
        @(posedge clk) ((S1 === 1'b1) && (S0 === 1'b0)) |-> (X === A2)
    );

    // S=11 routes A3 to X.
    check_select_11_routes_a3: assert property (
        @(posedge clk) ((S1 === 1'b1) && (S0 === 1'b1)) |-> (X === A3)
    );

    // With S=00 and A0 stable, X stays stable.
    check_select_00_stable_output: assert property (
        @(posedge clk) ((S1 === 1'b0) && (S0 === 1'b0) && $stable({S1, S0, A0})) |-> $stable(X)
    );

    // With S=01 and A1 stable, X stays stable.
    check_select_01_stable_output: assert property (
        @(posedge clk) ((S1 === 1'b0) && (S0 === 1'b1) && $stable({S1, S0, A1})) |-> $stable(X)
    );

    // With S=10 and A2 stable, X stays stable.
    check_select_10_stable_output: assert property (
        @(posedge clk) ((S1 === 1'b1) && (S0 === 1'b0) && $stable({S1, S0, A2})) |-> $stable(X)
    );

    // With S=11 and A3 stable, X stays stable.
    check_select_11_stable_output: assert property (
        @(posedge clk) ((S1 === 1'b1) && (S0 === 1'b1) && $stable({S1, S0, A3})) |-> $stable(X)
    );

    // If all functional inputs hold, X holds.
    check_all_functional_inputs_stable_hold_x: assert property (
        @(posedge clk) $stable({A0, A1, A2, A3, S0, S1}) |-> $stable(X)
    );

endmodule