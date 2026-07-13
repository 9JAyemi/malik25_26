module sqrt_calc_assertions (
    input logic [7:0] x,
    input logic [7:0] y,
    input logic [7:0] y_n,
    input logic [7:0] y_n1,
    input logic [7:0] x_int,
    input logic done
);

    // y_n starts from 8'h80.
    check_initial_estimate: assert property (
        @($global_clock) $initstate |-> (y_n == 8'h80)
    );

    // x_int mirrors the input x.
    check_x_int_matches_input: assert property (
        @($global_clock) x_int == x
    );

    // y_n1 follows the Newton-Raphson update expression.
    check_newton_step_computation: assert property (
        @($global_clock) (y_n != 8'h00) |-> (y_n1 == ((y_n + (x_int / y_n)) / 2))
    );

    // done can only be high inside the +/-1 convergence window.
    check_done_implies_converged: assert property (
        @($global_clock) done |-> ((y_n1 >= (y_n - 1)) && (y_n1 <= (y_n + 1)))
    );

    // The +/-1 convergence window drives done high.
    check_converged_sets_done: assert property (
        @($global_clock) ((y_n1 >= (y_n - 1)) && (y_n1 <= (y_n + 1))) |-> done
    );

    // The output y mirrors y_n1.
    check_output_matches_next_estimate: assert property (
        @($global_clock) y == y_n1
    );

endmodule

bind sqrt_calc sqrt_calc_assertions sqrt_calc_assertions_i (
    .x(x),
    .y(y),
    .y_n(y_n),
    .y_n1(y_n1),
    .x_int(x_int),
    .done(done)
);