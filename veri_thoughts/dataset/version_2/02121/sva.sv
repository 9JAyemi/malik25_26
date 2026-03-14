module absolute_value_sva (
    input logic clk,
    input logic [3:0] binary,
    input logic [3:0] abs_val
);
    // Analysis: No clock/reset in RTL; purely combinational absolute value function on 4-bit input.
    // Behavior: if binary[3]==1 then abs_val=(~binary+1)[3:0], else abs_val=binary.

    // Output equals mux of pass-through or two's complement based on sign bit.
    check_functional_select: assert property (
        @(posedge clk) abs_val == (binary[3] ? ((~binary + 4'b0001)[3:0]) : binary)
    );

    // When input is negative, output is the 2's complement of input (truncated to 4 bits).
    check_negative_path_twos_complement: assert property (
        @(posedge clk) binary[3] |-> (abs_val == ((~binary + 4'b0001)[3:0]))
    );

    // When input is non-negative, output equals input.
    check_positive_path_passthrough: assert property (
        @(posedge clk) !binary[3] |-> (abs_val == binary)
    );

    // Zero maps to zero.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) (binary == 4'd0) |-> (abs_val == 4'd0)
    );

    // Minimum negative (-8, 4'b1000) maps to 8 (4'b1000).
    check_minneg_maps_to_8: assert property (
        @(posedge clk) (binary == 4'b1000) |-> (abs_val == 4'b1000)
    );

    // For negative inputs except -8, the result has MSB 0.
    check_neg_nonmin_msb_zero: assert property (
        @(posedge clk) (binary[3] && (binary != 4'b1000)) |-> (abs_val[3] == 1'b0)
    );

    // For negative inputs except -8, the result is non-zero.
    check_neg_nonmin_nonzero: assert property (
        @(posedge clk) (binary[3] && (binary != 4'b1000)) |-> (abs_val != 4'd0)
    );

    // Output magnitude is always <= 8.
    check_output_range_le_8: assert property (
        @(posedge clk) abs_val <= 4'd8
    );

    // For non-negative inputs, the MSB of the output is 0.
    check_nonneg_msb_zero: assert property (
        @(posedge clk) !binary[3] |-> (abs_val[3] == 1'b0)
    );

    // Equivalent formulation: abs = (binary XOR sign-mask) + sign (truncated to 4 bits).
    check_xor_plus_sign_equivalence: assert property (
        @(posedge clk) abs_val == (((binary ^ {4{binary[3]}}) + {3'b000, binary[3]})[3:0])
    );

endmodule