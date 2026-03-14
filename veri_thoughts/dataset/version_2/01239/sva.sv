module comparator_and_xor_sva (
    input logic clk,           // verification clock for sampling assertions
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [1:0] out,
    input logic [3:0] xor_out
);
    // No reset in RTL; assertions use disable iff(1'b0). Purely combinational behavior.

    // Equal inputs drive out = 2'b00.
    check_out_eq_sets_00: assert property (
        @(posedge clk) disable iff (1'b0) (in1 == in2) |-> (out == 2'b00)
    );

    // in1 > in2 drives out = 2'b01.
    check_out_gt_sets_01: assert property (
        @(posedge clk) disable iff (1'b0) (in1 > in2) |-> (out == 2'b01)
    );

    // in1 < in2 drives out = 2'b10.
    check_out_lt_sets_10: assert property (
        @(posedge clk) disable iff (1'b0) (in1 < in2) |-> (out == 2'b10)
    );

    // out is never 2'b11.
    check_out_never_11: assert property (
        @(posedge clk) disable iff (1'b0) (out != 2'b11)
    );

    // out == 2'b00 implies inputs are equal.
    check_out00_implies_eq: assert property (
        @(posedge clk) disable iff (1'b0) (out == 2'b00) |-> (in1 == in2)
    );

    // out == 2'b01 implies in1 > in2.
    check_out01_implies_gt: assert property (
        @(posedge clk) disable iff (1'b0) (out == 2'b01) |-> (in1 > in2)
    );

    // out == 2'b10 implies in1 < in2.
    check_out10_implies_lt: assert property (
        @(posedge clk) disable iff (1'b0) (out == 2'b10) |-> (in1 < in2)
    );

    // xor_out equals bitwise XOR of in1 and in2.
    check_xor_definition: assert property (
        @(posedge clk) disable iff (1'b0) (xor_out == (in1 ^ in2))
    );

    // Equal inputs imply xor_out is zero.
    check_eq_implies_xor_zero: assert property (
        @(posedge clk) disable iff (1'b0) (in1 == in2) |-> (xor_out == 4'b0000)
    );

    // xor_out zero implies out == 2'b00.
    check_xor_zero_implies_out00: assert property (
        @(posedge clk) disable iff (1'b0) (xor_out == 4'b0000) |-> (out == 2'b00)
    );

    // If inputs are stable, outputs remain stable (purely combinational).
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(in1) && $stable(in2)) |-> ($stable(out) && $stable(xor_out))
    );

endmodule