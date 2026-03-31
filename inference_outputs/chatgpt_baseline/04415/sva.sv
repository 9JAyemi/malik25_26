module bitwise_or_sva (
    input logic       clock,
    input logic [7:0] a_in,
    input logic [7:0] b_in,
    input logic [7:0] out
);

    // out is the registered OR of the prior cycle inputs.
    check_out_matches_registered_or: assert property (
        @(posedge clock) disable iff ($initstate)
        out == ($past(a_in) | $past(b_in))
    );

    // Every 1 bit from the prior a_in must appear on out.
    check_a_bits_propagate_to_out: assert property (
        @(posedge clock) disable iff ($initstate)
        ($past(a_in) & ~out) == 8'h00
    );

    // Every 1 bit from the prior b_in must appear on out.
    check_b_bits_propagate_to_out: assert property (
        @(posedge clock) disable iff ($initstate)
        ($past(b_in) & ~out) == 8'h00
    );

    // out must not contain bits absent from both prior inputs.
    check_no_spurious_out_bits: assert property (
        @(posedge clock) disable iff ($initstate)
        (out & ~($past(a_in) | $past(b_in))) == 8'h00
    );

    // Zero inputs on a cycle must produce zero out on the next cycle.
    check_zero_inputs_yield_zero: assert property (
        @(posedge clock) disable iff ($initstate)
        (($past(a_in) == 8'h00) && ($past(b_in) == 8'h00)) |-> (out == 8'h00)
    );

endmodule