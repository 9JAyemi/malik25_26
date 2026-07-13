module adder_sva(
    input logic [3:0] A,
    input logic [3:0] B,
    input logic C_in,
    input logic [3:0] S,
    input logic C_out,
    input logic [4:0] sum,
    input logic C_out1
);

    // No clock or reset exists in the RTL; sample on the global formal clock.
    // The DUT is purely combinational.

    // S matches the low four bits of A + B + C_in.
    check_sum_low_bits: assert property (
        @($global_clock)
        ({1'b0, S} == (({1'b0, A} + {1'b0, B} + C_in) & 5'h0F))
    );

    // S is driven directly from sum[3:0].
    check_sum_slice_to_s: assert property (
        @($global_clock)
        (S == sum[3:0])
    );

    // C_out is the OR of sum[4] and C_out1.
    check_cout_or_relation: assert property (
        @($global_clock)
        (C_out == (sum[4] | C_out1))
    );

    // C_out1 matches the implemented reduction of sum[3:0].
    check_cout1_formula: assert property (
        @($global_clock)
        (C_out1 == (
            (sum[3] & sum[2]) |
            ((sum[3] | sum[2]) & sum[1]) |
            ((sum[3] | sum[2] | sum[1]) & sum[0])
        ))
    );

    // An arithmetic carry from A + B + C_in must raise C_out.
    check_cout_on_arithmetic_carry: assert property (
        @($global_clock)
        ((({1'b0, A} + {1'b0, B} + C_in) & 5'h10) != 5'h00) |-> C_out
    );

    // sum[4] alone is sufficient to raise C_out.
    check_cout_on_sum_msb: assert property (
        @($global_clock)
        sum[4] |-> C_out
    );

    // sum[3] and sum[2] high force C_out1 high.
    check_cout1_on_top_pair: assert property (
        @($global_clock)
        (sum[3] & sum[2]) |-> C_out1
    );

    // sum[1] with either sum[3] or sum[2] high forces C_out1 high.
    check_cout1_on_mid_pair: assert property (
        @($global_clock)
        ((sum[3] | sum[2]) & sum[1]) |-> C_out1
    );

    // sum[0] with any higher sum bit high forces C_out1 high.
    check_cout1_on_low_pair: assert property (
        @($global_clock)
        ((sum[3] | sum[2] | sum[1]) & sum[0]) |-> C_out1
    );

    // With neither source active, C_out must stay low.
    check_cout_low_without_sources: assert property (
        @($global_clock)
        (!sum[4] && !C_out1) |-> !C_out
    );

endmodule