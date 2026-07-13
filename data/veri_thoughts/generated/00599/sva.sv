module ripple_carry_adder_sva (
    input  logic        CLK,
    input  logic [3:0]  in0,
    input  logic [3:0]  in1,
    input  logic        carry_in,
    input  logic [3:0]  sum,
    input  logic        carry_out
);

    // Helper expressions for ripple carries and full 5-bit result
    let c0   = (in0[0] & in1[0]) | (in0[0] & carry_in) | (in1[0] & carry_in);
    let c1   = (in0[1] & in1[1]) | (in0[1] & c0)       | (in1[1] & c0);
    let c2   = (in0[2] & in1[2]) | (in0[2] & c1)       | (in1[2] & c1);
    let res5 = ({1'b0,in0} + {1'b0,in1} + carry_in);

    // The 5-bit {carry_out,sum} equals in0 + in1 + carry_in.
    check_add_result_5bit: assert property (
        @(posedge CLK) disable iff (1'b0) {carry_out, sum} == res5
    );

    // sum[0] equals XOR of LSBs and carry_in.
    check_sum0_xor: assert property (
        @(posedge CLK) disable iff (1'b0) sum[0] == (in0[0] ^ in1[0] ^ carry_in)
    );

    // sum[1] equals XOR of bit1s and carry from bit0.
    check_sum1_xor: assert property (
        @(posedge CLK) disable iff (1'b0) sum[1] == (in0[1] ^ in1[1] ^ c0)
    );

    // sum[2] equals XOR of bit2s and carry from bit1.
    check_sum2_xor: assert property (
        @(posedge CLK) disable iff (1'b0) sum[2] == (in0[2] ^ in1[2] ^ c1)
    );

    // sum[3] equals XOR of bit3s and carry from bit2.
    check_sum3_xor: assert property (
        @(posedge CLK) disable iff (1'b0) sum[3] == (in0[3] ^ in1[3] ^ c2)
    );

    // carry_out is the majority of bit3s and carry from bit2.
    check_carry_out_majority: assert property (
        @(posedge CLK) disable iff (1'b0) carry_out == ((in0[3] & in1[3]) | (in0[3] & c2) | (in1[3] & c2))
    );

    // The 4-bit sum equals the low 4 bits of the arithmetic result.
    check_sum_low_bits_match: assert property (
        @(posedge CLK) disable iff (1'b0) sum == res5[3:0]
    );

    // If inputs are stable across a cycle, outputs remain stable.
    check_stability_on_stable_inputs: assert property (
        @(posedge CLK) disable iff (1'b0)
            (in0 == $past(in0) && in1 == $past(in1) && carry_in == $past(carry_in))
            |-> (sum == $past(sum) && carry_out == $past(carry_out))
    );

    // With in0/in1 stable, a rising carry_in increments the 5-bit result by 1.
    check_increment_on_cin_rise: assert property (
        @(posedge CLK) disable iff (1'b0)
            (in0 == $past(in0) && in1 == $past(in1) && $rose(carry_in))
            |-> ({carry_out, sum} == $past({carry_out, sum}) + 5'd1)
    );

    // With in0/in1 stable, a falling carry_in decrements the 5-bit result by 1.
    check_decrement_on_cin_fall: assert property (
        @(posedge CLK) disable iff (1'b0)
            (in0 == $past(in0) && in1 == $past(in1) && $fell(carry_in))
            |-> ({carry_out, sum} == $past({carry_out, sum}) - 5'd1)
    );

endmodule