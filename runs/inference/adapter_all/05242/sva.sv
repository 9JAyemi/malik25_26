module bitwise_operators_sva #(
    parameter int n = 8
) (
    input logic clk,
    input logic [n-1:0] a,
    input logic [n-1:0] b,
    input logic [n-1:0] and_out,
    input logic [n-1:0] or_out,
    input logic [n-1:0] xor_out,
    input logic [n-1:0] not_out
);

    // and_out must equal the bitwise AND of a and b.
    check_and_function: assert property (
        @(posedge clk) and_out == (a & b)
    );

    // or_out must equal the bitwise OR of a and b.
    check_or_function: assert property (
        @(posedge clk) or_out == (a | b)
    );

    // xor_out must equal the bitwise XOR of a and b.
    check_xor_function: assert property (
        @(posedge clk) xor_out == (a ^ b)
    );

    // not_out must equal the bitwise NOT of a.
    check_not_function: assert property (
        @(posedge clk) not_out == (~a)
    );

    // The outputs must remain stable when a and b are stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable({and_out, or_out, xor_out, not_out})
    );

    // and_out must change only when a or b changes.
    check_and_output_change_requires_input_change: assert property (
        @(posedge clk) $changed(and_out) |-> ($changed(a) || $changed(b))
    );

    // or_out must change only when a or b changes.
    check_or_output_change_requires_input_change: assert property (
        @(posedge clk) $changed(or_out) |-> ($changed(a) || $changed(b))
    );

    // xor_out must change only when a or b changes.
    check_xor_output_change_requires_input_change: assert property (
        @(posedge clk) $changed(xor_out) |-> ($changed(a) || $changed(b))
    );

    // not_out must change only when a changes.
    check_not_output_change_requires_input_change: assert property (
        @(posedge clk) $changed(not_out) |-> $changed(a)
    );

endmodule