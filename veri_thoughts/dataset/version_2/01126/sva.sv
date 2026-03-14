module bitwise_xor_sva (
    input logic        clk,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic [7:0]  out
);
    ///// Functional relationship /////
    // Output equals XOR of inputs from previous cycle.
    check_out_matches_prev_xor: assert property (
        @(posedge clk) disable iff ($initstate) out == ($past(a) ^ $past(b))
    );

    // If inputs are stable over a cycle, output stays stable into the next cycle.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff ($initstate) ($stable(a) && $stable(b)) |=> $stable(out)
    );

    // If only 'a' changes and 'b' is stable over a cycle, output changes next cycle.
    check_vector_change_due_to_a_only: assert property (
        @(posedge clk) disable iff ($initstate) ($changed(a) && $stable(b)) |=> $changed(out)
    );

    // If only 'b' changes and 'a' is stable over a cycle, output changes next cycle.
    check_vector_change_due_to_b_only: assert property (
        @(posedge clk) disable iff ($initstate) ($changed(b) && $stable(a)) |=> $changed(out)
    );

    // Per-bit XOR: equal bits yield 0 in next cycle, different bits yield 1 in next cycle.
    genvar i;
    generate
        for (i = 0; i < 8; i++) begin : gen_bit_xor_checks
            // If a[i] equals b[i] at sample, next-cycle out[i] is 0.
            check_bit_equal_implies_zero: assert property (
                @(posedge clk) disable iff ($initstate) (a[i] == b[i]) |=> (out[i] == 1'b0)
            );
            // If a[i] differs from b[i] at sample, next-cycle out[i] is 1.
            check_bit_diff_implies_one: assert property (
                @(posedge clk) disable iff ($initstate) (a[i] != b[i]) |=> (out[i] == 1'b1)
            );
        end
    endgenerate
endmodule