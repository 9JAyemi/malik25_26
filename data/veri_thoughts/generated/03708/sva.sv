module sky130_fd_sc_ls__o21a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic EN
);

    // X must match the implemented combinational function.
    check_x_matches_o21a_function: assert property (
        @($global_clock) X == (EN ? (A1 & A2 & B1) : 1'b0)
    );

    // When EN is low, X must be low.
    check_x_low_when_disabled: assert property (
        @($global_clock) (!EN) |-> (X == 1'b0)
    );

    // With EN high, A1 low must force X low.
    check_x_low_when_a1_low: assert property (
        @($global_clock) (EN && !A1) |-> (X == 1'b0)
    );

    // With EN high, A2 low must force X low.
    check_x_low_when_a2_low: assert property (
        @($global_clock) (EN && !A2) |-> (X == 1'b0)
    );

    // With EN high, B1 low must force X low.
    check_x_low_when_b1_low: assert property (
        @($global_clock) (EN && !B1) |-> (X == 1'b0)
    );

    // When EN and all inputs are high, X must be high.
    check_x_high_when_all_inputs_high: assert property (
        @($global_clock) (EN && A1 && A2 && B1) |-> (X == 1'b1)
    );

endmodule