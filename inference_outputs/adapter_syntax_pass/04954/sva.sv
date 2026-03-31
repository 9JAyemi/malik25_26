module pipelined_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] OUT
);

    // OUT is the registered sum of A and B from two cycles earlier.
    check_out_two_cycle_sum: assert property (
        @(posedge clk) 1'b1 |-> ##2 (OUT == ($past(A, 2) + $past(B, 2)))
    );

    // A zero A operand produces zero OUT two cycles later.
    check_zero_a_path: assert property (
        @(posedge clk) (A == 4'h0) |-> ##2 (OUT == 4'h0)
    );

    // A zero B operand produces zero OUT two cycles later.
    check_zero_b_path: assert property (
        @(posedge clk) (B == 4'h0) |-> ##2 (OUT == 4'h0)
    );

    // Stable A and B inputs keep OUT stable two cycles later.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> ##2 $stable(OUT)
    );

    // A zero OUT two cycles later means both A and B were zero.
    check_zero_output_implies_zero_inputs: assert property (
        @(posedge clk) 1'b1 |-> ##2 ((OUT == 4'h0) |-> (($past(A, 2) == 4'h0) && ($past(B, 2) == 4'h0)))
    );

    // A carry from bit 2 propagates to bit 3 in OUT two cycles later.
    check_carry_propagation: assert property (
        @(posedge clk) 1'b1 |-> ##2 ((($past(A, 2) + $past(B, 2)) >= 5'd16) |-> (OUT[3] == 1'b1))
    );

endmodule