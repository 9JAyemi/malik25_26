module priority_encoder_sva (
    input logic clk,          // sampling clock for assertions
    input logic [7:0] in,
    input logic [2:0] pos
);
    // pos equals bitwise inversion of in[2:0].
    check_pos_inversion_vector: assert property (
        @(posedge clk) pos == ~in[2:0]
    );

    // pos[0] equals ~in[0].
    check_pos0_inversion: assert property (
        @(posedge clk) pos[0] == ~in[0]
    );

    // pos[1] equals ~in[1].
    check_pos1_inversion: assert property (
        @(posedge clk) pos[1] == ~in[1]
    );

    // pos[2] equals ~in[2].
    check_pos2_inversion: assert property (
        @(posedge clk) pos[2] == ~in[2]
    );

    // pos remains stable if in[2:0] is stable.
    check_pos_stable_when_lower3_stable: assert property (
        @(posedge clk) $stable(in[2:0]) |-> $stable(pos)
    );

    // pos changes whenever in[2:0] changes.
    check_pos_changes_with_lower3: assert property (
        @(posedge clk) $changed(in[2:0]) |-> $changed(pos)
    );

    // Changing in[7:3] alone does not affect pos.
    check_upper_bits_irrelevant: assert property (
        @(posedge clk) $changed(in[7:3]) && $stable(in[2:0]) |-> $stable(pos)
    );
endmodule