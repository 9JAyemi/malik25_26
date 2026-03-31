module top_module_sva (
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] out,
    input logic [3:0] max_out
);

    // out is the 4-bit sum of in1 and in2.
    check_out_matches_sum: assert property (
        @($global_clock) out == (in1 + in2)
    );

    // max_out is the 4-bit maximum of out and the 4-bit sum of in1 and in2.
    check_max_out_matches_max_function: assert property (
        @($global_clock) max_out == ((out > (in1 + in2)) ? out : (in1 + in2))
    );

    // max_out is always at least the 4-bit sum of in1 and in2.
    check_max_out_is_at_least_sum: assert property (
        @($global_clock) max_out >= (in1 + in2)
    );

    // max_out is always at least the 4-bit value of out.
    check_max_out_is_at_least_out: assert property (
        @($global_clock) max_out >= out
    );

    // max_out is always at least the 4-bit value of in1.
    check_max_out_is_at_least_in1: assert property (
        @($global_clock) max_out >= in1
    );

    // max_out is always at least the 4-bit value of in2.
    check_max_out_is_at_least_in2: assert property (
        @($global_clock) max_out >= in2
    );

    // max_out is always within the 4-bit range.
    check_max_out_is_4bit: assert property (
        @($global_clock) max_out <= 4'hF
    );

endmodule