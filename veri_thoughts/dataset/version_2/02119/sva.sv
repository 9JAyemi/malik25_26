module xor_gate_lut_sva (
    input logic CLK,
    input logic a,
    input logic b,
    input logic out_lut
);
    // Output equals XOR of inputs each cycle.
    check_out_eq_xor: assert property (
        @(posedge CLK) (out_lut == (a ^ b))
    );

    // Truth table: 00 -> 0.
    check_case_00: assert property (
        @(posedge CLK) ({a,b} == 2'b00) |-> (out_lut == 1'b0)
    );
    // Truth table: 01 -> 1.
    check_case_01: assert property (
        @(posedge CLK) ({a,b} == 2'b01) |-> (out_lut == 1'b1)
    );
    // Truth table: 10 -> 1.
    check_case_10: assert property (
        @(posedge CLK) ({a,b} == 2'b10) |-> (out_lut == 1'b1)
    );
    // Truth table: 11 -> 0.
    check_case_11: assert property (
        @(posedge CLK) ({a,b} == 2'b11) |-> (out_lut == 1'b0)
    );

    // When b is 0, output passes a.
    check_b0_passthrough: assert property (
        @(posedge CLK) (b == 1'b0) |-> (out_lut == a)
    );
    // When b is 1, output is inverted a.
    check_b1_invert: assert property (
        @(posedge CLK) (b == 1'b1) |-> (out_lut == ~a)
    );

    // When a is 0, output passes b.
    check_a0_passthrough: assert property (
        @(posedge CLK) (a == 1'b0) |-> (out_lut == b)
    );
    // When a is 1, output is inverted b.
    check_a1_invert: assert property (
        @(posedge CLK) (a == 1'b1) |-> (out_lut == ~b)
    );

    // If inputs are stable between samples, output is stable.
    check_stability: assert property (
        @(posedge CLK) ($stable(a) && $stable(b)) |-> $stable(out_lut)
    );

    // Output change parity equals XOR of input changes between samples.
    check_change_parity: assert property (
        @(posedge CLK) ($changed(out_lut) == ($changed(a) ^ $changed(b)))
    );
endmodule