module nor_using_nand_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);
    // Output implements NAND: out == ~(a & b).
    check_nand_function: assert property (
        @(posedge clk) out == (~(a & b))
    );

    // When both inputs are 1, out is 0.
    check_tt_11_zero: assert property (
        @(posedge clk) (a && b) |-> (out == 1'b0)
    );

    // When any input is 0, out is 1.
    check_any_zero_high: assert property (
        @(posedge clk) ((!a) || (!b)) |-> (out == 1'b1)
    );

    // Out low only if both inputs are 1.
    check_low_only_when_both_one: assert property (
        @(posedge clk) (out == 1'b0) |-> (a && b)
    );

    // DeMorgan equivalence form: out == (~a) || (~b).
    check_demorgan_form: assert property (
        @(posedge clk) out == ((~a) || (~b))
    );

    // If inputs are stable between cycles, output is stable.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk) $stable({a, b}) |-> $stable(out)
    );

    // Output changes only if at least one input changes.
    check_output_change_needs_input_change: assert property (
        @(posedge clk) $changed(out) |-> ($changed(a) || $changed(b))
    );
endmodule