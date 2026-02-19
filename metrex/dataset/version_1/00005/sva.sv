module top_module_assertions (
    input  logic        clk,
    input  logic        reset,    // Top-level reset
    input  logic [7:0]  a,
    input  logic [7:0]  b,
    input  logic [3:0]  data,
    input  logic        select,
    input  logic [7:0]  s,
    input  logic        overflow
);
    //==========================================================================
    // Analysis summary:
    // - Clock: clk
    // - Reset: The only sequential block in the hierarchy is shift_register,
    //           which uses an ASYNCHRONOUS ACTIVE-LOW reset driven by 'reset'.
    //           Therefore, assertions are disabled when reset==0.
    // - Logic type: Mixed
    //     * Combinational: sign-magnitude conversion (a_mag/b_mag), carry_select_adder
    //     * Sequential: 4-bit shift_register (enable=1, load=0, shifts left when select=1)
    // - Key behaviors:
    //     * a_mag/b_mag: convert two's-complement to sign-magnitude with MSB forced to 0.
    //     * Adder (cin=0): s_adder8 = (a_mag + b_mag) + ((a_mag & b_mag) << 1)
    //       overflow_adder = (a_mag[7] == b_mag[7]) && (s_adder8[7] != a_mag[7]).
    //       Since a_mag[7]==b_mag[7]==0 always, overflow simplifies to s_adder8[7].
    //     * Output mux: if select==0 -> s = s_adder8; if select==1 -> s = {4'b0, shift_q}
    //       Hence when select==1, s[7:4]==4'b0 always. With shift_left active, s[0]==0.
    //==========================================================================

    // Helper: two's-complement to sign-magnitude (matches RTL width behavior)
    function automatic logic [7:0] to_sm8 (input logic [7:0] x);
        logic [6:0] mag7;
        begin
            mag7   = (~x[6:0]) + 7'd1;
            to_sm8 = x[7] ? {1'b0, mag7} : x;
        end
    endfunction

    // Helper: adder result for cin==0 (matches carry_select_adder RTL path)
    function automatic logic [7:0] adder_u8 (input logic [7:0] aa, input logic [7:0] bb);
        logic [7:0] p, g;
        begin
            p       = aa + bb;
            g       = aa & bb;
            adder_u8 = p + (g << 1);
        end
    endfunction

    // Helper: expected 8-bit adder output from top-level inputs a,b
    function automatic logic [7:0] adder_expected_sum8 (input logic [7:0] a_in, input logic [7:0] b_in);
        logic [7:0] aa, bb;
        begin
            aa = to_sm8(a_in);
            bb = to_sm8(b_in);
            adder_expected_sum8 = adder_u8(aa, bb);
        end
    endfunction

    // Helper: expected overflow from top-level inputs a,b (matches carry_select_adder)
    function automatic logic overflow_expected (input logic [7:0] a_in, input logic [7:0] b_in);
        logic [7:0] aa, bb, sum8;
        begin
            aa = to_sm8(a_in);
            bb = to_sm8(b_in);
            sum8 = adder_u8(aa, bb);
            overflow_expected = (aa[7] == bb[7]) && (sum8[7] != aa[7]); // simplifies to sum8[7]
        end
    endfunction

    ///// Output mux rules /////
    // When select==0, s must equal the adder's 8-bit result computed from sign-magnitude inputs.
    check_mux_select0_adder_value: assert property (
        @(posedge clk) disable iff (!reset)
            (select == 1'b0) |-> (s == adder_expected_sum8(a, b))
    );

    // When select==1, upper nibble of s is always zero due to {4'b0, shift_out}.
    check_shift_path_upper_zero: assert property (
        @(posedge clk) disable iff (!reset)
            (select == 1'b1) |-> (s[7:4] == 4'b0000)
    );

    // When select==1, the LSB of s is always zero because shift_left inserts 0.
    check_shift_path_lsb_zero: assert property (
        @(posedge clk) disable iff (!reset)
            (select == 1'b1) |-> (s[0] == 1'b0)
    );

    ///// Shift register dynamic behavior (observed through s when select==1) /////
    // If select stays 1 for two consecutive cycles, the low nibble of s left-shifts by 1 with zero fill.
    // Note: Consequent is checked on the 2nd cycle; $past(s[2:0]) refers to the prior cycle's low 3 bits.
    check_shift_left_single_step: assert property (
        @(posedge clk) disable iff (!reset)
            (select ##1 select) |-> (s[7:4] == 4'b0000 && s[3:0] == {$past(s[2:0]), 1'b0})
    );

    // If select stays 1 for 5 consecutive cycles, the 4-bit shift register must have shifted out all bits to zero.
    // (We check on the 5th cycle so the updated state is observable at the sampled edge.)
    check_shift_clears_in_five: assert property (
        @(posedge clk) disable iff (!reset)
            (select [*5]) |-> (s[7:4] == 4'b0000 && s[3:0] == 4'b0000)
    );

    ///// Adder/overflow rules /////
    // Overflow output must match the adder's definition from the RTL (with a_mag/b_mag inputs and cin=0).
    check_overflow_definition: assert property (
        @(posedge clk) disable iff (!reset)
            overflow == overflow_expected(a, b)
    );

    // Since a_mag[7]==b_mag[7]==0 for this design, overflow reduces to the adder sum bit7.
    // Therefore, when the adder path is selected, overflow equals s[7].
    check_overflow_equals_s7_when_select0: assert property (
        @(posedge clk) disable iff (!reset)
            (select == 1'b0) |-> (overflow == s[7])
    );

    // In adder mode, if inputs a and b are stable across cycles, s must remain stable (independent of data/select history).
    check_adder_mode_stability_when_ab_stable: assert property (
        @(posedge clk) disable iff (!reset)
            (select == 1'b0 && $past(select) == 1'b0 && $stable(a) && $stable(b)) |-> $stable(s)
    );

    // In adder mode, s does not depend on 'data'. If a and b are stable but data toggles, s must remain stable.
    check_no_data_dependency_in_adder_mode: assert property (
        @(posedge clk) disable iff (!reset)
            (select == 1'b0 && $past(select) == 1'b0 && $stable(a) && $stable(b) && !$stable(data)) |-> $stable(s)
    );

    // Commutativity sanity for the specific adder path used by the DUT:
    // Swapping a and b (with select==0 in consecutive cycles) yields the same s.
    check_adder_commutativity_observed: assert property (
        @(posedge clk) disable iff (!reset)
            (select == 1'b0 && $past(select) == 1'b0 && (a == $past(b)) && (b == $past(a))) |-> (s == $past(s))
    );

endmodule