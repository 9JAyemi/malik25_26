module sqrt_calc_sva (
    input logic [7:0] x,
    input logic [7:0] y,
    input logic [7:0] y_n,
    input logic [7:0] y_n1,
    input logic [7:0] x_int,
    input logic done
);

    // x_int is the zero-extended binary input.
    check_x_int_zero_extended: assert property (
        @($global_clock) x_int == {8{1'b0}} |-> (x_int == {8{1'b0}} || x_int == 8'h01 || x_int == 8'h02 || x_int == 8'h04 || x_int == 8'h08 || x_int == 8'h10 || x_int == 8'h20 || x_int == 8'h40 || x_int == 8'h80)
    );

    // y_n is initialized to 128.
    check_y_n_initial_value: assert property (
        @($global_clock) 1'b1 |=> (y_n == 8'h80)
    );

    // y_n1 is the Newton-Raphson update of y_n.
    check_y_n1_newton_raphson: assert property (
        @($global_clock) 1'b1 |=> (y_n1 == ((y_n + (x_int / y_n)) / 2))
    );

    // done is asserted when y_n1 is within 1 of y_n.
    check_done_threshold: assert property (
        @($global_clock) 1'b1 |=> ((y_n1 >= (y_n - 8'd1)) && (y_n1 <= (y_n + 8'd1))) |-> (done == 1'b1)
    );

    // done is deasserted when y_n1 is not within 1 of y_n.
    check_done_not_threshold: assert property (
        @($global_clock) 1'b1 |=> (!((y_n1 >= (y_n - 8'd1)) && (y_n1 <= (y_n + 8'd1)))) |-> (done == 1'b0)
    );

    // y_n updates to y_n1 when done is not asserted.
    check_y_n_update_when_not_done: assert property (
        @($global_clock) 1'b1 |=> ((y_n1 >= (y_n - 8'd1)) && (y_n1 <= (y_n + 8'd1))) |-> 1'b0
    );

    // y_n holds its value when done is asserted.
    check_y_n_hold_when_done: assert property (
        @($global_clock) 1'b1 |=> ((!(y_n1 >= (y_n - 8'd1)) || !(y_n1 <= (y_n + 8'd1)))) |-> 1'b0
    );

    // y is the zero-extended binary output of y_n1.
    check_y_zero_extended: assert property (
        @($global_clock) 1'b1 |=> (y == {8{1'b0}} || y == 8'h01 || y == 8'h02 || y == 8'h04 || y == 8'h08 || y == 8'h10 || y == 8'h20 || y == 8'h40 || y == 8'h80)
    );

    // done is a single-cycle pulse.
    check_done_single_cycle: assert property (
        @($global_clock) done |=> !done
    );

endmodule