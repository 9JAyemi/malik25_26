module top_module_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic reset,
    input logic out
);

    // Reset forces the top-level output low.
    check_reset_forces_out_low: assert property (
        @(posedge a or posedge b or posedge c or posedge reset)
        reset |-> (out == 1'b0)
    );

    // With reset low, the output matches the XOR of a and b gated by c.
    check_output_matches_xor_and_c: assert property (
        @(posedge a or posedge b or posedge c or posedge reset)
        !reset |-> (out == ((a ^ b) & c))
    );

    // When c is low, the output must be low.
    check_c_low_forces_out_low: assert property (
        @(posedge a or posedge b or posedge c or posedge reset)
        !c |-> (out == 1'b0)
    );

    // When c is high, the output reduces to the XOR of a and b.
    check_c_high_passes_xor: assert property (
        @(posedge a or posedge b or posedge c or posedge reset)
        c |-> (out == (a ^ b))
    );

    // With reset low and c high, a low XOR result forces the output low.
    check_xor_zero_forces_out_low: assert property (
        @(posedge a or posedge b or posedge c or posedge reset)
        (!reset && c && !(a ^ b)) |-> (out == 1'b0)
    );

    // With reset low and c high, a high XOR result forces the output high.
    check_xor_one_forces_out_high: assert property (
        @(posedge a or posedge b or posedge c or posedge reset)
        (!reset && c && (a ^ b)) |-> (out == 1'b1)
    );

endmodule