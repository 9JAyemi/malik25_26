module pipelined_vector_sva (
    input logic [2:0] vec,
    input logic clk,
    input logic [2:0] outv,
    input logic o2,
    input logic o1,
    input logic o0,
    input logic [2:0] stage1_out,
    input logic [2:0] stage2_out,
    input logic [2:0] stage3_out
);

    // Direct outputs mirror the input vector bits.
    check_passthrough_bits: assert property (
        @(posedge clk) {o2, o1, o0} == vec
    );

    // First pipeline stage captures vec on each clock.
    check_stage1_captures_vec: assert property (
        @(posedge clk) disable iff ($initstate)
        stage1_out == $past(vec)
    );

    // Second pipeline stage captures the previous stage1 value.
    check_stage2_captures_stage1: assert property (
        @(posedge clk) disable iff ($initstate)
        stage2_out == $past(stage1_out)
    );

    // Third pipeline stage captures the previous stage2 value.
    check_stage3_captures_stage2: assert property (
        @(posedge clk) disable iff ($initstate)
        stage3_out == $past(stage2_out)
    );

    // outv is a direct copy of the third pipeline stage.
    check_outv_matches_stage3: assert property (
        @(posedge clk) outv == stage3_out
    );

    // outv is vec delayed by three clock cycles.
    check_outv_three_cycle_delay: assert property (
        @(posedge clk) disable iff ($initstate || $past($initstate) || $past($initstate,2))
        outv == $past(vec,3)
    );

endmodule