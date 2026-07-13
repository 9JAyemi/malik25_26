module xnor_nand_assertions (
    input logic a,
    input logic b,
    input logic out
);

    // Output is low when both inputs are low.
    check_00_drives_low: assert property (
        @($global_clock) ((a == 1'b0) && (b == 1'b0)) |-> (out == 1'b0)
    );

    // Output is high when only b is high.
    check_01_drives_high: assert property (
        @($global_clock) ((a == 1'b0) && (b == 1'b1)) |-> (out == 1'b1)
    );

    // Output is high when only a is high.
    check_10_drives_high: assert property (
        @($global_clock) ((a == 1'b1) && (b == 1'b0)) |-> (out == 1'b1)
    );

    // Output is low when both inputs are high.
    check_11_drives_low: assert property (
        @($global_clock) ((a == 1'b1) && (b == 1'b1)) |-> (out == 1'b0)
    );

    // Output always matches the XOR of the inputs.
    check_out_matches_xor: assert property (
        @($global_clock) out == (a ^ b)
    );

endmodule