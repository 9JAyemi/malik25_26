module RippleAdder0_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic ci,
    input logic co,
    input logic [3:0] s
);

    // Carry-out is driven from bit 0 of a.
    check_carry_out_matches_a0: assert property (
        @(posedge clk) co == a[0]
    );

    // Sum bit 0 mirrors the carry-in.
    check_sum_bit0_matches_carry_in: assert property (
        @(posedge clk) s[0] == ci
    );

    // Sum bit 1 mirrors bit 0 of a.
    check_sum_bit1_matches_a0: assert property (
        @(posedge clk) s[1] == a[0]
    );

    // Sum bit 2 mirrors bit 0 of a.
    check_sum_bit2_matches_a0: assert property (
        @(posedge clk) s[2] == a[0]
    );

    // Sum bit 3 mirrors bit 0 of a.
    check_sum_bit3_matches_a0: assert property (
        @(posedge clk) s[3] == a[0]
    );

    // Upper sum bits all match the carry-out.
    check_upper_sum_bits_match_carry_out: assert property (
        @(posedge clk) s[3:1] == {3{co}}
    );

    // Sum vector is three copies of co followed by ci.
    check_sum_vector_structure: assert property (
        @(posedge clk) s == {co, co, co, ci}
    );

    // Full output mapping depends only on a[0] and ci.
    check_full_output_mapping: assert property (
        @(posedge clk) {co, s} == {{4{a[0]}}, ci}
    );

endmodule