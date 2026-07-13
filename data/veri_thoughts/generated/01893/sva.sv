module adder_4bit_sva (
    input logic clk,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] out,
    input logic carry
);
    // {carry,out} equals 5-bit zero-extended sum of inputs.
    check_full_sum_5bit: assert property (
        @(posedge clk) {carry, out} == ({1'b0, in1} + {1'b0, in2})
    );

    // LSB sum is XOR of inputs (carry_in = 0).
    check_lsb_xor: assert property (
        @(posedge clk) out[0] == (in1[0] ^ in2[0])
    );

    // Bit1 sum includes carry from bit0 = in1[0]&in2[0].
    check_bit1_sum_with_carry0: assert property (
        @(posedge clk) out[1] == (in1[1] ^ in2[1] ^ (in1[0] & in2[0]))
    );

    // Bit2 sum with ripple carry from lower bits.
    check_bit2_sum_with_ripple: assert property (
        @(posedge clk)
            out[2] == (
                in1[2] ^ in2[2] ^
                ( (in1[1] & in2[1]) | ((in1[1] ^ in2[1]) & (in1[0] & in2[0])) )
            )
    );

    // Bit3 sum with ripple carry from lower bits.
    check_bit3_sum_with_ripple: assert property (
        @(posedge clk)
            out[3] == (
                in1[3] ^ in2[3] ^
                ( (in1[2] & in2[2]) | ((in1[2] ^ in2[2]) &
                    ( (in1[1] & in2[1]) | ((in1[1] ^ in2[1]) & (in1[0] & in2[0])) )
                  )
                )
            )
    );

    // Final carry equals ripple-carry chain from bit3.
    check_carry_chain_formula: assert property (
        @(posedge clk)
            carry == (
                (in1[3] & in2[3]) | ((in1[3] ^ in2[3]) &
                    ( (in1[2] & in2[2]) | ((in1[2] ^ in2[2]) &
                        ( (in1[1] & in2[1]) | ((in1[1] ^ in2[1]) & (in1[0] & in2[0])) )
                      )
                    )
                )
            )
    );

    // Carry equals MSB of 5-bit zero-extended sum.
    check_carry_is_msb_of_sum: assert property (
        @(posedge clk) carry == (({1'b0, in1} + {1'b0, in2})[4])
    );

    // Outputs remain stable when inputs are stable across cycles.
    check_outputs_stable_if_inputs_stable: assert property (
        @(posedge clk) ($stable(in1) && $stable(in2)) |-> ($stable(out) && $stable(carry))
    );

    // Right identity: adding zero on in2 yields out=in1 and carry=0.
    check_add_zero_right_identity: assert property (
        @(posedge clk) (in2 == 4'b0000) |-> (out == in1 && carry == 1'b0)
    );

    // Left identity: adding zero on in1 yields out=in2 and carry=0.
    check_add_zero_left_identity: assert property (
        @(posedge clk) (in1 == 4'b0000) |-> (out == in2 && carry == 1'b0)
    );
endmodule