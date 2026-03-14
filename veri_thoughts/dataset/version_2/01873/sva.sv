module parity_sva #(
    parameter int unsigned n = 8
) (
    input  logic               clk,
    input  logic [n-1:0]       in,
    input  logic               p,
    input  logic [n-1:0]       out
);
    // out must mirror in exactly (bitwise).
    check_out_equals_in: assert property (
        @(posedge clk) out === in
    );

    // p must equal the reduction XOR of in.
    check_p_equals_xor_in: assert property (
        @(posedge clk) p === (^in)
    );

    // p must also equal the reduction XOR of out (since out == in).
    check_p_equals_xor_out: assert property (
        @(posedge clk) p === (^out)
    );

    // When in is all zeros, p must be 0 and out must be all zeros.
    check_zero_input_behavior: assert property (
        @(posedge clk) (in === '0) |-> (p === 1'b0) && (out === '0)
    );

    // When in is all ones, p must equal n%2 and out must be all ones.
    localparam bit P_ONES = (n % 2) ? 1'b1 : 1'b0;
    check_all_ones_input_behavior: assert property (
        @(posedge clk) (in === {n{1'b1}}) |-> (p === P_ONES) && (out === {n{1'b1}})
    );

    // When exactly one input bit is 1, p must be 1 and out must equal in.
    check_onehot_sets_parity: assert property (
        @(posedge clk) $onehot(in) |-> (p === 1'b1) && (out === in)
    );

    // If inputs are stable this cycle, outputs must be stable.
    check_stable_out_when_in_stable: assert property (
        @(posedge clk) $stable(in) |-> $stable(out)
    );

    // If inputs are stable this cycle, parity output must be stable.
    check_stable_p_when_in_stable: assert property (
        @(posedge clk) $stable(in) |-> $stable(p)
    );

    // If inputs change, outputs must change (since out mirrors in).
    check_changed_in_implies_changed_out: assert property (
        @(posedge clk) $changed(in) |-> $changed(out)
    );

    // If outputs change, inputs must have changed (no internal storage/logic).
    check_changed_out_implies_changed_in: assert property (
        @(posedge clk) $changed(out) |-> $changed(in)
    );
endmodule