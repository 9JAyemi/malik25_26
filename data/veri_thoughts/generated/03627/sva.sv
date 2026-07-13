module top_module_sva(
    input logic [4:0] in,
    input logic select,
    input logic out_and,
    input logic out_or,
    input logic out_nor
);

    // The shared input/select bits make the top-level AND output always low.
    check_out_and_always_low: assert property (
        @($global_clock)
        out_and == 1'b0
    );

    // The OR output is high only for the enabled decoder code 01.
    check_out_or_matches_decode: assert property (
        @($global_clock)
        out_or == (select && (in[1:0] == 2'b01))
    );

    // The NOR output is low only for the enabled decoder code 10.
    check_out_nor_matches_decode: assert property (
        @($global_clock)
        out_nor == !(select && (in[1:0] == 2'b10))
    );

    // With select low, AND and OR are low and the disabled NOR output is high.
    check_select_low_defaults: assert property (
        @($global_clock)
        !select |-> ((out_and == 1'b0) && (out_or == 1'b0) && (out_nor == 1'b1))
    );

    // Decoder code 00 selects the AND path, but the shared low bits force it low.
    check_code00_behavior: assert property (
        @($global_clock)
        (select && (in[1:0] == 2'b00)) |-> ((out_and == 1'b0) && (out_or == 1'b0) && (out_nor == 1'b1))
    );

    // Decoder code 01 selects the OR path, and the shared low bit forces it high.
    check_code01_behavior: assert property (
        @($global_clock)
        (select && (in[1:0] == 2'b01)) |-> ((out_and == 1'b0) && (out_or == 1'b1) && (out_nor == 1'b1))
    );

    // Decoder code 10 selects the NOR path, and the shared high bit forces it low.
    check_code10_behavior: assert property (
        @($global_clock)
        (select && (in[1:0] == 2'b10)) |-> ((out_and == 1'b0) && (out_or == 1'b0) && (out_nor == 1'b0))
    );

    // Decoder code 11 drives an unused decoder output, so these outputs stay at defaults.
    check_code11_behavior: assert property (
        @($global_clock)
        (select && (in[1:0] == 2'b11)) |-> ((out_and == 1'b0) && (out_or == 1'b0) && (out_nor == 1'b1))
    );

endmodule