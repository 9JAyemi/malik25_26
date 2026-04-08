module mult_by_3_sva (
    input logic clk,
    input logic [3:0] x,
    input logic [5:0] y
);

    // y must always equal the RTL expression.
    check_y_matches_rtl_expression: assert property (
        @(posedge clk) y == ((x << 1) + x)
    );

    // The least-significant output bit must match the least-significant input bit.
    check_lsb_preserved: assert property (
        @(posedge clk) y[0] == x[0]
    );

    // Zero input must produce zero output.
    check_x_zero: assert property (
        @(posedge clk) (x == 4'd0) |-> (y == 6'd0)
    );

    // Input value one must produce three.
    check_x_one: assert property (
        @(posedge clk) (x == 4'd1) |-> (y == 6'd3)
    );

    // Input value two must produce six.
    check_x_two: assert property (
        @(posedge clk) (x == 4'd2) |-> (y == 6'd6)
    );

    // Input value three must produce nine.
    check_x_three: assert property (
        @(posedge clk) (x == 4'd3) |-> (y == 6'd9)
    );

    // Input value four must produce twelve.
    check_x_four: assert property (
        @(posedge clk) (x == 4'd4) |-> (y == 6'd12)
    );

    // Input value five must produce fifteen.
    check_x_five: assert property (
        @(posedge clk) (x == 4'd5) |-> (y == 6'd15)
    );

endmodule