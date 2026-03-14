module twos_complement_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] in,
    input logic [3:0] out
);
    // Clock: clk. Reset: reset (active-high, synchronous).
    // Logic: mixed (combinational two's complement into registered out).

    ///// Reset behavior /////
    // After a cycle with reset=1, out must be 0 on the next sampled cycle.
    check_out_zero_after_prev_reset: assert property (
        @(posedge clk) disable iff (reset) $past(reset) |-> (out == 4'b0000)
    );

    // On the cycle reset deasserts (1->0), out must be 0 (held from prior reset cycle).
    check_out_zero_on_reset_fall: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> (out == 4'b0000)
    );

    ///// Functional mapping (two's complement) /////
    // After a cycle with reset=0, out equals (~in + 1) of the previous cycle (registered).
    check_out_equals_twos_comp_of_prev_in: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (out == ((~$past(in) + 4'b0001)[3:0]))
    );

    // LSB mapping: after non-reset, out[0] equals prior in[0].
    check_lsb_matches_prev_in: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (out[0] == $past(in[0]))
    );

    // When prior in[0]==1 (no carry propagation), out[3:1] == ~in[3:1].
    check_upper_invert_when_prev_lsb1: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && $past(in[0])) |-> (out[3:1] == ~$past(in[3:1]))
    );

    // When prior in[0]==0 and in[1]==1 (carry stops at bit1), out[3:2] == ~in[3:2].
    check_bits32_invert_when_prev_lsb0_bit1_1: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && !$past(in[0]) && $past(in[1])) |-> (out[3:2] == ~$past(in[3:2]))
    );

    // When prior in[0:2]==3'b001 (carry stops at bit2), out[3] == ~in[3].
    check_bit3_invert_when_prev_lowbits_001: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && !$past(in[0]) && !$past(in[1]) && $past(in[2])) |-> (out[3] == ~$past(in[3]))
    );

    // Additive inverse property: after non-reset, out + in == 16 (mod 16).
    check_additive_inverse_mod16: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (({1'b0, out} + {1'b0, $past(in)}) == 5'd16)
    );

    // Special case: after non-reset, in==4'b1000 maps to out==4'b1000.
    check_self_inverse_for_8: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && ($past(in) == 4'b1000)) |-> (out == 4'b1000)
    );

    // Special case: after non-reset, in==0 maps to out==0.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && ($past(in) == 4'b0000)) |-> (out == 4'b0000)
    );
endmodule