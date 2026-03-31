module sqrt_calc_sva (
    input logic [7:0] x,
    input logic [7:0] y,
    input logic [7:0] y_n,
    input logic [7:0] y_n1,
    input logic [7:0] x_int,
    input logic done
);

    // x_int is the zero-extended input value.
    check_x_int_zero_extension: assert property (
        @($global_clock) x_int == {8'b0, x}
    );

    // y_n starts at the initialized value of 128.
    check_y_n_initial_value: assert property (
        @($global_clock) $initstate |-> (y_n == 8'h80)
    );

    // y_n1 is the Newton-Raphson update of y_n.
    check_y_n1_newton_raphson: assert property (
        @($global_clock) y_n1 == ((y_n + x_int / y_n) >> 1)
    );

    // done is high when y_n1 is within 1 of y_n.
    check_done_within_tolerance: assert property (
        @($global_clock) (y_n1 >= y_n - 1 && y_n1 <= y_n + 1) |-> done
    );

    // done is low when y_n1 is not within 1 of y_n.
    check_done_outside_tolerance: assert property (
        @($global_clock) !(y_n1 >= y_n - 1 && y_n1 <= y_n + 1) |-> !done
    );

    // y is the zero-extended value of y_n1.
    check_y_zero_extension: assert property (
        @($global_clock) y == {8'b0, y_n1}
    );

    // done is high when y is within 1 of the current estimate.
    check_done_matches_output_tolerance: assert property (
        @($global_clock) (y >= y_n - 1 && y <= y_n + 1) |-> done
    );

    // done is low when y is not within 1 of the current estimate.
    check_done_not_matches_output_tolerance: assert property (
        @($global_clock) !(y >= y_n - 1 && y <= y_n + 1) |-> !done
    );

    // done is high when y_n1 is within 1 of y_n1.
    check_done_self_tolerance: assert property (
        @($global_clock) (y_n1 >= y_n1 - 1 && y_n1 <= y_n1 + 1) |-> done
    );

    // done is low when y_n1 is not within 1 of y_n1.
    check_done_self_not_tolerance: assert property (
        @($global_clock) !(y_n1 >= y_n1 - 1 && y_n1 <= y_n1 + 1) |-> !done
    );

endmodule