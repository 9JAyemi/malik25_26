module comparator_sva (
    input logic       clk,
    input logic       comp1,
    input logic [5:0] v1_reg
);

    // comp1 matches the combinational function implemented by the RTL.
    check_comp1_function: assert property (
        @(posedge clk)
        comp1 == (
            ((v1_reg[5:4] == 2'b00) && ((v1_reg[3:0] + 4'b0001) >= 4'h8)) ||
            (v1_reg[5:4] == 2'b01) ||
            ((v1_reg[5:4] == 2'b10) && !((v1_reg[3:0] + 4'b0001) >= 4'h8))
        )
    );

    // Upper bits 01 force comp1 high.
    check_upper_01_sets_comp1: assert property (
        @(posedge clk)
        (v1_reg[5:4] == 2'b01) |-> (comp1 == 1'b1)
    );

    // Upper bits 11 force comp1 low.
    check_upper_11_clears_comp1: assert property (
        @(posedge clk)
        (v1_reg[5:4] == 2'b11) |-> (comp1 == 1'b0)
    );

    // Upper bits 00 make comp1 follow bit[3] of the low-nibble increment.
    check_upper_00_uses_low_increment_msb: assert property (
        @(posedge clk)
        (v1_reg[5:4] == 2'b00) |-> (comp1 == ((v1_reg[3:0] + 4'b0001) >= 4'h8))
    );

    // Upper bits 10 make comp1 invert bit[3] of the low-nibble increment.
    check_upper_10_inverts_low_increment_msb: assert property (
        @(posedge clk)
        (v1_reg[5:4] == 2'b10) |-> (comp1 == !((v1_reg[3:0] + 4'b0001) >= 4'h8))
    );

    // If the input vector is unchanged, the sampled output must also remain unchanged.
    check_stable_input_gives_stable_output: assert property (
        @(posedge clk)
        $stable(v1_reg) |-> $stable(comp1)
    );

endmodule