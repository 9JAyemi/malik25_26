// Add these SVA blocks inside the given modules (concise, quality-focused)

// ========================= top_module SVA =========================
/* place at end of module top_module, before endmodule */
    // Default SVA clock/disable
    property DIS; disable iff (reset) 1; endproperty

    // Byte reverse correctness
    assert property (@(posedge clk) DIS |-> (A_reversed == {A[7:0], A[15:8], A[23:16], A[31:24]}));
    assert property (@(posedge clk) DIS |-> (B_reversed == {B[7:0], B[15:8], B[23:16], B[31:24]}));

    // Bitwise ops
    assert property (@(posedge clk) DIS |-> (A_xor_B == (A ^ B)));
    assert property (@(posedge clk) DIS |-> (A_and_B == (A & B)));

    // Shifts
    assert property (@(posedge clk) DIS |-> (A_and_B_shifted == (A_and_B << 1)));
    assert property (@(posedge clk) DIS |-> (A_xor_B_shifted == (A_xor_B << 1)));

    // Adder 1 (functional intent: accurate 33-bit addition)
    assert property (@(posedge clk) DIS |-> (A_xor_B_shifted_and_carry_out == ({1'b0,A_xor_B} + {1'b0,A_and_B_shifted})[31:0]));
    assert property (@(posedge clk) DIS |-> (carry_out == ({1'b0,A_xor_B} + {1'b0,A_and_B_shifted})[32]));

    // Adder 2 (functional intent: accurate 33-bit addition)
    assert property (@(posedge clk) DIS |-> (sum == ({1'b0,A_xor_B_shifted} + {1'b0,A_and_B_shifted})[31:0]));

    // 8-bit multiplier and post-processing
    assert property (@(posedge clk) DIS |-> (product == (sum[7:0] * A_reversed[7:0])));
    assert property (@(posedge clk) DIS |-> (result_shifted == ((product << 1)[7:0])));
    assert property (@(posedge clk) DIS |-> (result == (result_shifted ^ B_reversed[7:0])));

    // Sanity: no X on key outputs
    assert property (@(posedge clk) DIS |-> !$isunknown({result, result_shifted, product, carry_out, sum}));

    // High-value coverage
    cover property (@(posedge clk) !reset && carry_out);
    cover property (@(posedge clk) !reset && (({1'b0,A_xor_B}+{1'b0,A_and_B_shifted})[32])); // rca1 addition overflow
    cover property (@(posedge clk) !reset && product[15]);   // mul MSB set
    cover property (@(posedge clk) !reset && (result == 8'h00));
    cover property (@(posedge clk) !reset && (result == 8'hFF));

// ===================== ripple_carry_adder SVA =====================
/* place at end of module ripple_carry_adder, before endmodule */
    // Default SVA clock/disable
    property DIS; disable iff (reset) 1; endproperty

    // Golden adder check (unsigned 33-bit addition)
    assert property (@(posedge clk) DIS |-> ({carry_out, sum} == ({1'b0, A} + {1'b0, B})));

    // Carry chain structure
    assert property (@(posedge clk) DIS |-> (carry[0] == 1'b0));
    generate
        genvar gi;
        for (gi = 0; gi < 31; gi++) begin : carry_chk
            assert property (@(posedge clk) DIS |-> (carry[gi+1] == ((A[gi] & B[gi]) | (A[gi] & carry[gi]) | (B[gi] & carry[gi]))));
        end
    endgenerate

    // Sanity: no X on outputs
    assert property (@(posedge clk) DIS |-> !$isunknown({sum, carry_out}));

    // Coverage: overflow and zero-sum
    cover property (@(posedge clk) !reset && carry_out);
    cover property (@(posedge clk) !reset && (sum == 32'h0000_0000));