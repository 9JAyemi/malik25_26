module full_adder_sva(
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic        cin,
    input logic [15:0] out,
    input logic        cout
);

    // Combined outputs equal the 17-bit addition result.
    check_full_sum: assert property (
        @($global_clock)
        {cout, out} == ({1'b0, in1} + {1'b0, in2} + {16'b0, cin})
    );

    // The 16-bit sum output matches the truncated addition result.
    check_out_truncation: assert property (
        @($global_clock)
        out == (in1 + in2 + cin)
    );

    // The carry output indicates overflow beyond 16 bits.
    check_cout_overflow: assert property (
        @($global_clock)
        cout == (({1'b0, in1} + {1'b0, in2} + {16'b0, cin}) > 17'h0FFFF)
    );

    // Zero inputs produce a zero result.
    check_zero_case: assert property (
        @($global_clock)
        ((in1 == 16'h0000) && (in2 == 16'h0000) && (cin == 1'b0)) |-> ((out == 16'h0000) && (cout == 1'b0))
    );

    // Adding zero with no carry passes in1 through unchanged.
    check_in1_passthrough: assert property (
        @($global_clock)
        ((in2 == 16'h0000) && (cin == 1'b0)) |-> ((out == in1) && (cout == 1'b0))
    );

    // Adding zero with no carry passes in2 through unchanged.
    check_in2_passthrough: assert property (
        @($global_clock)
        ((in1 == 16'h0000) && (cin == 1'b0)) |-> ((out == in2) && (cout == 1'b0))
    );

    // Maximum inputs with carry-in generate all ones and a carry-out.
    check_max_overflow_case: assert property (
        @($global_clock)
        ((in1 == 16'hFFFF) && (in2 == 16'hFFFF) && (cin == 1'b1)) |-> ((out == 16'hFFFF) && (cout == 1'b1))
    );

endmodule