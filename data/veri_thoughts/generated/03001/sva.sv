module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic reset,
    input logic Clk,
    input logic Clk_180,
    input logic [3:0] S,
    input logic Cout
);

    // While reset is asserted, both registered outputs are zero.
    check_reset_clears_outputs: assert property (
        @(posedge Clk) reset |-> ({Cout, S} == 5'b0)
    );

    // The first sampled clock after reset was high still sees cleared outputs.
    check_post_reset_sampled_outputs_zero: assert property (
        @(posedge Clk) disable iff (reset || $initstate)
        $past(reset) |-> ({Cout, S} == 5'b0)
    );

    // Outside reset, outputs are either reset-cleared or the prior clocked computation.
    check_outputs_are_zero_or_prior_computation: assert property (
        @(posedge Clk) disable iff (reset || $initstate)
        (({Cout, S} == 5'b0) ||
         ({Cout, S} == {
            $past(((A[3] & B[3]) | (Cin & (A[3] | B[3])))),
            $past(A + B + Cin)
         }))
    );

    // Any non-zero output state must come from the prior clocked computation.
    check_nonzero_outputs_match_prior_computation: assert property (
        @(posedge Clk) disable iff (reset || $initstate)
        ({Cout, S} != 5'b0) |-> ({Cout, S} == {
            $past(((A[3] & B[3]) | (Cin & (A[3] | B[3])))),
            $past(A + B + Cin)
        })
    );

endmodule