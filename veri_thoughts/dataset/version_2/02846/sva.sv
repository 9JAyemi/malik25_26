module bitwise_and_sva #(
    parameter bits = 16
) (
    input logic clk,
    input logic [bits-1:0] a,
    input logic [bits-1:0] b,
    input logic [bits-1:0] q
);
    // q equals bitwise AND of a and b each cycle.
    check_bitwise_and_equivalence: assert property (
        @(posedge clk) q == (a & b)
    );

    // q cannot have 1s where a has 0s.
    check_q_masked_by_a: assert property (
        @(posedge clk) (q & ~a) == {bits{1'b0}}
    );

    // q cannot have 1s where b has 0s.
    check_q_masked_by_b: assert property (
        @(posedge clk) (q & ~b) == {bits{1'b0}}
    );

    // If a is all zeros, q must be all zeros.
    check_zero_a_forces_zero_q: assert property (
        @(posedge clk) (a == {bits{1'b0}}) |-> (q == {bits{1'b0}})
    );

    // If b is all zeros, q must be all zeros.
    check_zero_b_forces_zero_q: assert property (
        @(posedge clk) (b == {bits{1'b0}}) |-> (q == {bits{1'b0}})
    );

    // If a is all ones, q passes b.
    check_all_ones_a_passes_b: assert property (
        @(posedge clk) (a == {bits{1'b1}}) |-> (q == b)
    );

    // If b is all ones, q passes a.
    check_all_ones_b_passes_a: assert property (
        @(posedge clk) (b == {bits{1'b1}}) |-> (q == a)
    );

    // If both inputs are stable, q must be stable.
    check_q_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable(q)
    );

    // If q changed, at least one input changed.
    check_q_change_implies_input_change: assert property (
        @(posedge clk) $changed(q) |-> ($changed(a) || $changed(b))
    );
endmodule