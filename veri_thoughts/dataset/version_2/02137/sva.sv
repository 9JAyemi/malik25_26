module top_module_sva (
    input logic clk,         // sampling clock for SVA (DUT has no clock)
    input logic a,
    input logic b,
    input logic sel_xor,
    input logic sel_mux,
    input logic out_always
);
    // Functional equivalence to the RTL ternary chain.
    check_function_equivalence: assert property (
        @(posedge clk)
        out_always == ((sel_xor & ~sel_mux) ? (a ^ b) :
                       (sel_mux & ~sel_xor) ? b :
                       (sel_mux & sel_xor)  ? 1'b1 : 1'b0)
    );

    // When sel_xor=1 and sel_mux=0, output is XOR of a and b.
    check_case_sel10_xor: assert property (
        @(posedge clk) (sel_xor && !sel_mux) |-> (out_always == (a ^ b))
    );

    // When sel_xor=0 and sel_mux=1, output is b (2:1 mux selects b).
    check_case_sel01_b: assert property (
        @(posedge clk) (sel_mux && !sel_xor) |-> (out_always == b)
    );

    // When sel_xor=1 and sel_mux=1, output is constant 1.
    check_case_sel11_one: assert property (
        @(posedge clk) (sel_mux && sel_xor) |-> (out_always == 1'b1)
    );

    // When sel_xor=0 and sel_mux=0, output is constant 0.
    check_case_sel00_zero: assert property (
        @(posedge clk) (!sel_mux && !sel_xor) |-> (out_always == 1'b0)
    );

    // In mux-only case (01), if sel and b are stable, output must be stable (independent of a).
    check_stability_mux_case: assert property (
        @(posedge clk)
        (sel_mux && !sel_xor && $stable(sel_mux) && $stable(sel_xor) && $stable(b)) |-> $stable(out_always)
    );

    // In both-high case (11), if sel remain 11, output stays 1 and stable.
    check_stability_both_high: assert property (
        @(posedge clk)
        (sel_mux && sel_xor && $stable(sel_mux) && $stable(sel_xor)) |-> ($stable(out_always) && (out_always == 1'b1))
    );

    // In both-low case (00), if sel remain 00, output stays 0 and stable.
    check_stability_both_low: assert property (
        @(posedge clk)
        (!sel_mux && !sel_xor && $stable(sel_mux) && $stable(sel_xor)) |-> ($stable(out_always) && (out_always == 1'b0))
    );

    // If all inputs are stable, the output must be stable (purely combinational behavior).
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk)
        ($stable(a) && $stable(b) && $stable(sel_xor) && $stable(sel_mux)) |-> $stable(out_always)
    );
endmodule