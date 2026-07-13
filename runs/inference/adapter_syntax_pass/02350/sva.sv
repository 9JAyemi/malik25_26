module top_module_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic reset,
    input logic out
);

    // out matches the implemented combinational function.
    check_out_matches_function: assert property (
        @($global_clock) disable iff (reset)
        out == ((a ^ b) & (c | reset))
    );

    // A reset cycle forces the OR stage low, so out must be low.
    check_out_low_during_reset: assert property (
        @($global_clock)
        reset |-> (out == 1'b0)
    );

    // With reset low, out reduces to c AND (a XOR b).
    check_out_reduces_to_c_and_xor_when_not_reset: assert property (
        @($global_clock) disable iff (reset)
        out == (c & (a ^ b))
    );

    // A low c forces the OR stage low, so out must be low.
    check_out_low_when_c_low: assert property (
        @($global_clock) disable iff (reset)
        !c |-> (out == 1'b0)
    );

    // Equal a and b force the XOR stage low, so out must be low.
    check_out_low_when_a_equals_b: assert property (
        @($global_clock) disable iff (reset)
        (a == b) |-> (out == 1'b0)
    );

    // With reset low and c high, out follows a XOR b.
    check_out_follows_xor_when_c_high_and_not_reset: assert property (
        @($global_clock) disable iff (reset)
        (c && !reset) |-> (out == (a ^ b))
    );

    // With reset low and a XOR b high, out follows c.
    check_out_follows_c_when_xor_high_and_not_reset: assert property (
        @($global_clock) disable iff (reset)
        ((a ^ b) && !reset) |-> (out == c)
    );

endmodule