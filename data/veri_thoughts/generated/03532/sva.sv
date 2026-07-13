module xor_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic control,
    input logic out
);

    // Output matches the gated XOR function.
    check_gated_xor_function: assert property (
        @(posedge clk) out == (control ? (a ^ b) : 1'b0)
    );

    // Output is forced low when control is deasserted.
    check_control_low_forces_zero: assert property (
        @(posedge clk) !control |-> (out == 1'b0)
    );

    // Output equals a XOR b when control is asserted.
    check_control_high_passes_xor: assert property (
        @(posedge clk) control |-> (out == (a ^ b))
    );

    // With control asserted, equal inputs produce a low output.
    check_equal_inputs_drive_low: assert property (
        @(posedge clk) (control && (a == b)) |-> (out == 1'b0)
    );

    // With control asserted, different inputs produce a high output.
    check_different_inputs_drive_high: assert property (
        @(posedge clk) (control && (a != b)) |-> (out == 1'b1)
    );

endmodule