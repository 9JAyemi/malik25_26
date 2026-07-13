module combinational_circuit_sva(
    input logic [3:0] A,
    input logic [1:0] B,
    input logic C,
    input logic D,
    input logic E,
    input logic X
);

    // X is high when A is at most 5 and B equals 2.
    check_x_from_ab_condition: assert property (
        @($global_clock)
        ((A <= 4'd5) && (B == 2'd2)) |-> (X == 1'b1)
    );

    // X is high when C is high, D is low, and E is high.
    check_x_from_cde_condition: assert property (
        @($global_clock)
        ((C == 1'b1) && (D == 1'b0) && (E == 1'b1)) |-> (X == 1'b1)
    );

    // X is low when neither implemented condition is true.
    check_x_low_when_no_condition_matches: assert property (
        @($global_clock)
        !(((A <= 4'd5) && (B == 2'd2)) ||
          ((C == 1'b1) && (D == 1'b0) && (E == 1'b1))) |-> (X == 1'b0)
    );

    // X can only be high when one implemented condition is true.
    check_x_only_from_implemented_conditions: assert property (
        @($global_clock)
        (X == 1'b1) |-> (((A <= 4'd5) && (B == 2'd2)) ||
                         ((C == 1'b1) && (D == 1'b0) && (E == 1'b1)))
    );

    // X matches the full combinational function.
    check_x_matches_function: assert property (
        @($global_clock)
        X == (((A <= 4'd5) && (B == 2'd2)) ||
              ((C == 1'b1) && (D == 1'b0) && (E == 1'b1)))
    );

endmodule