module custom_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);
    // On A1 rising, X must be 0 (X = ~A1).
    x_eq_not_a1_on_a1_rise: assert property (
        @(posedge A1) (X == 1'b0)
    );

    // On A1 falling, X must be 1 (X = ~A1).
    x_eq_not_a1_on_a1_fall: assert property (
        @(negedge A1) (X == 1'b1)
    );

    // X equals ~A1 on A2 rising.
    x_eq_not_a1_on_a2_rise: assert property (
        @(posedge A2) (X == ~A1)
    );

    // X equals ~A1 on A2 falling.
    x_eq_not_a1_on_a2_fall: assert property (
        @(negedge A2) (X == ~A1)
    );

    // X equals ~A1 on A3 rising.
    x_eq_not_a1_on_a3_rise: assert property (
        @(posedge A3) (X == ~A1)
    );

    // X equals ~A1 on A3 falling.
    x_eq_not_a1_on_a3_fall: assert property (
        @(negedge A3) (X == ~A1)
    );

    // X equals ~A1 on A4 rising.
    x_eq_not_a1_on_a4_rise: assert property (
        @(posedge A4) (X == ~A1)
    );

    // X equals ~A1 on A4 falling.
    x_eq_not_a1_on_a4_fall: assert property (
        @(negedge A4) (X == ~A1)
    );

    // X equals ~A1 on B1 rising.
    x_eq_not_a1_on_b1_rise: assert property (
        @(posedge B1) (X == ~A1)
    );

    // X equals ~A1 on B1 falling.
    x_eq_not_a1_on_b1_fall: assert property (
        @(negedge B1) (X == ~A1)
    );
endmodule