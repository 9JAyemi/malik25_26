module test_lookahead_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c_in,
    input logic sum,
    input logic c_out
);

    // Sum must match the RTL combinational equation.
    check_sum_equation: assert property (
        @(posedge clk)
        sum == ((~a & ~b) ^ (c_in ^ (a & b)))
    );

    // Carry-out must match the RTL combinational equation.
    check_cout_equation: assert property (
        @(posedge clk)
        c_out == ((a & b) | ((~a & ~b) & c_in))
    );

    // When both inputs are 0, sum inverts c_in and carry-out follows c_in.
    check_both_zero_behavior: assert property (
        @(posedge clk)
        ((!a) && (!b)) |-> ((sum == (~c_in)) && (c_out == c_in))
    );

    // When both inputs are 1, sum inverts c_in and carry-out is asserted.
    check_both_one_behavior: assert property (
        @(posedge clk)
        (a && b) |-> ((sum == (~c_in)) && (c_out == 1'b1))
    );

    // When inputs differ, sum follows c_in and carry-out is deasserted.
    check_mismatched_inputs_behavior: assert property (
        @(posedge clk)
        (a ^ b) |-> ((sum == c_in) && (c_out == 1'b0))
    );

endmodule