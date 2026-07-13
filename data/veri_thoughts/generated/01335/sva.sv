module ripple_carry_adder_sva #(
    parameter BITS = 8
) (
    input logic                  clock,
    input logic [BITS-1:0]       a_in,
    input logic [BITS-1:0]       b_in,
    input logic [BITS-1:0]       out
);
    // No reset in RTL; assertions are clocked on 'clock'.

    // Sum equals truncated addition of inputs.
    check_sum_correct: assert property (
        @(posedge clock) out == (a_in + b_in)
    );

    // If b_in is zero, out equals a_in.
    check_add_zero_b: assert property (
        @(posedge clock) (b_in == '0) |-> (out == a_in)
    );

    // If a_in is zero, out equals b_in.
    check_add_zero_a: assert property (
        @(posedge clock) (a_in == '0) |-> (out == b_in)
    );

    // LSB sum equals XOR of LSB inputs (carry-in is 0).
    check_lsb_xor: assert property (
        @(posedge clock) out[0] == (a_in[0] ^ b_in[0])
    );

    // If both LSB inputs are 1, LSB sum is 0.
    check_lsb_carry_effect: assert property (
        @(posedge clock) (a_in[0] & b_in[0]) |-> (out[0] == 1'b0)
    );

    // Adding bitwise complement yields all ones.
    check_complement_all_ones: assert property (
        @(posedge clock) (b_in == ~a_in) |-> (out == {BITS{1'b1}})
    );

    // All ones plus 1 wraps to zero (a_in = all 1s, b_in = 1).
    check_ones_plus_one_wrap_a: assert property (
        @(posedge clock)
            (a_in == {BITS{1'b1}}) && (b_in == {{(BITS-1){1'b0}},1'b1}) |-> (out == {BITS{1'b0}})
    );

    // All ones plus 1 wraps to zero (b_in = all 1s, a_in = 1).
    check_ones_plus_one_wrap_b: assert property (
        @(posedge clock)
            (b_in == {BITS{1'b1}}) && (a_in == {{(BITS-1){1'b0}},1'b1}) |-> (out == {BITS{1'b0}})
    );

    // When inputs are equal, result is left shift by 1 (modulo width).
    check_double_when_equal: assert property (
        @(posedge clock) (a_in == b_in) |-> (out == (a_in << 1))
    );

    // Lower 2-bit slice adds correctly (independent of higher bits).
    if (BITS >= 2) begin : gen_low2
        check_low2_slice_sum: assert property (
            @(posedge clock) out[1:0] == (a_in[1:0] + b_in[1:0])
        );
        // Bit1 sum equals XOR of bit1s and carry from bit0 (a0 & b0).
        check_bit1_sum: assert property (
            @(posedge clock) out[1] == (a_in[1] ^ b_in[1]) ^ (a_in[0] & b_in[0])
        );
    end

    // Lower 3-bit slice adds correctly (independent of higher bits).
    if (BITS >= 3) begin : gen_low3
        check_low3_slice_sum: assert property (
            @(posedge clock) out[2:0] == (a_in[2:0] + b_in[2:0])
        );
    end
endmodule