module MUX4_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S0,
    input logic S1,
    input logic Y
);

    // Y matches the nested mux equation implemented by the RTL.
    check_full_mux_equation: assert property (
        @(posedge clk)
        Y === ((S1 == 1'b0) ? ((S0 == 1'b0) ? A : B)
                            : ((S0 == 1'b0) ? C : D))
    );

    // When S1 is low, Y must come from the A/B mux selected by S0.
    check_lower_pair_when_s1_low: assert property (
        @(posedge clk)
        (S1 === 1'b0) |-> (Y === ((S0 == 1'b0) ? A : B))
    );

    // When S1 is high, Y must come from the C/D mux selected by S0.
    check_upper_pair_when_s1_high: assert property (
        @(posedge clk)
        (S1 === 1'b1) |-> (Y === ((S0 == 1'b0) ? C : D))
    );

    // Selecting S1=0 and S0=0 routes A to Y.
    check_select_a_path: assert property (
        @(posedge clk)
        ((S1 === 1'b0) && (S0 === 1'b0)) |-> (Y === A)
    );

    // Selecting S1=0 and S0=1 routes B to Y.
    check_select_b_path: assert property (
        @(posedge clk)
        ((S1 === 1'b0) && (S0 === 1'b1)) |-> (Y === B)
    );

    // Selecting S1=1 and S0=0 routes C to Y.
    check_select_c_path: assert property (
        @(posedge clk)
        ((S1 === 1'b1) && (S0 === 1'b0)) |-> (Y === C)
    );

    // Selecting S1=1 and S0=1 routes D to Y.
    check_select_d_path: assert property (
        @(posedge clk)
        ((S1 === 1'b1) && (S0 === 1'b1)) |-> (Y === D)
    );

endmodule