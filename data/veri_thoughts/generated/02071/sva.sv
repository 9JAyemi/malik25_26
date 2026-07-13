module logic_unit_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic x
);

    // x implements the 2-of-3 majority of a,b,c.
    check_x_majority_function: assert property (
        @(posedge clk) x == ((a & b) | (a & c) | (b & c))
    );

    // If a and b are 1, x must be 1.
    check_x_when_ab: assert property (
        @(posedge clk) (a && b) |-> x
    );

    // If a and c are 1, x must be 1.
    check_x_when_ac: assert property (
        @(posedge clk) (a && c) |-> x
    );

    // If b and c are 1, x must be 1.
    check_x_when_bc: assert property (
        @(posedge clk) (b && c) |-> x
    );

    // If only a is 1, x must be 0.
    check_x_when_only_a: assert property (
        @(posedge clk) (a && !b && !c) |-> !x
    );

    // If only b is 1, x must be 0.
    check_x_when_only_b: assert property (
        @(posedge clk) (b && !a && !c) |-> !x
    );

    // If only c is 1, x must be 0.
    check_x_when_only_c: assert property (
        @(posedge clk) (c && !a && !b) |-> !x
    );

    // If all are 0, x must be 0.
    check_x_when_all_zero: assert property (
        @(posedge clk) (!a && !b && !c) |-> !x
    );

    // If all are 1, x must be 1.
    check_x_when_all_one: assert property (
        @(posedge clk) (a && b && c) |-> x
    );

    // x can be 1 only if at least two inputs are 1.
    check_x_implies_two_high: assert property (
        @(posedge clk) x |-> ((a && b) || (a && c) || (b && c))
    );

endmodule