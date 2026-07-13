module nor_gate_sva (
    input logic clk,   // SVA clock (DUT has no clock/reset)
    input logic a,
    input logic b,
    input logic out
);
    // out implements (~a | b).
    check_func_equiv: assert property (
        @(posedge clk) out == ((~a) | b)
    );

    // If a is LOW, out must be HIGH.
    check_a0_implies_out1: assert property (
        @(posedge clk) (a == 1'b0) |-> (out == 1'b1)
    );

    // If b is HIGH, out must be HIGH.
    check_b1_implies_out1: assert property (
        @(posedge clk) (b == 1'b1) |-> (out == 1'b1)
    );

    // If a is HIGH and b is LOW, out must be LOW.
    check_a1b0_implies_out0: assert property (
        @(posedge clk) (a == 1'b1 && b == 1'b0) |-> (out == 1'b0)
    );

    // If both a and b are HIGH, out must be HIGH.
    check_a1b1_implies_out1: assert property (
        @(posedge clk) (a == 1'b1 && b == 1'b1) |-> (out == 1'b1)
    );

    // If both a and b are LOW, out must be HIGH.
    check_a0b0_implies_out1: assert property (
        @(posedge clk) (a == 1'b0 && b == 1'b0) |-> (out == 1'b1)
    );

    // If a is LOW and b is HIGH, out must be HIGH.
    check_a0b1_implies_out1: assert property (
        @(posedge clk) (a == 1'b0 && b == 1'b1) |-> (out == 1'b1)
    );

    // If out is LOW, then a must be HIGH and b must be LOW.
    check_out0_only_when_a1b0: assert property (
        @(posedge clk) (out == 1'b0) |-> (a == 1'b1 && b == 1'b0)
    );
endmodule