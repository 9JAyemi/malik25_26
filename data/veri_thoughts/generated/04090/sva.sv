module top_module_assertions (
    input logic CLK,
    input logic CLR,
    input logic LD,
    input logic [3:0] DATA,
    input logic [3:0] Y,
    input logic [3:0] counter_output,
    input logic [3:0] bitwise_and_output
);

    // Active-low reset forces the counter and both combinational outputs to zero.
    check_reset_clears_all: assert property (
        @(posedge CLK) !CLR |-> (counter_output == 4'd0 && bitwise_and_output == 4'd0 && Y == 4'd0)
    );

    // The first sampled cycle after reset release still reflects the cleared state.
    check_reset_release_starts_zero: assert property (
        @(posedge CLK) disable iff (!CLR)
        $rose(CLR) |-> (counter_output == 4'd0 && bitwise_and_output == 4'd0 && Y == 4'd0)
    );

    // The bitwise_and block outputs counter_output AND DATA.
    check_bitwise_and_function: assert property (
        @(posedge CLK) disable iff (!CLR)
        bitwise_and_output == (counter_output & DATA)
    );

    // The functional_module outputs bitwise_and_output AND counter_output.
    check_final_output_function: assert property (
        @(posedge CLK) disable iff (!CLR)
        Y == (bitwise_and_output & counter_output)
    );

    // The final output matches the intermediate AND result.
    check_output_matches_intermediate: assert property (
        @(posedge CLK) disable iff (!CLR)
        Y == bitwise_and_output
    );

    // The top-level output equals counter_output masked by DATA.
    check_output_mask_relation: assert property (
        @(posedge CLK) disable iff (!CLR)
        Y == (counter_output & DATA)
    );

    // Zero DATA forces both combinational outputs low.
    check_zero_data_forces_zero_output: assert property (
        @(posedge CLK) disable iff (!CLR)
        (DATA == 4'd0) |-> (bitwise_and_output == 4'd0 && Y == 4'd0)
    );

    // All-ones DATA passes counter_output through both combinational stages.
    check_all_ones_data_passes_counter: assert property (
        @(posedge CLK) disable iff (!CLR)
        (DATA == 4'hF) |-> (bitwise_and_output == counter_output && Y == counter_output)
    );

    // All-ones counter_output passes DATA through both combinational stages.
    check_all_ones_counter_passes_data: assert property (
        @(posedge CLK) disable iff (!CLR)
        (counter_output == 4'hF) |-> (bitwise_and_output == DATA && Y == DATA)
    );

endmodule

bind top_module top_module_assertions top_module_assertions_inst (
    .CLK(CLK),
    .CLR(CLR),
    .LD(LD),
    .DATA(DATA),
    .Y(Y),
    .counter_output(counter_output),
    .bitwise_and_output(bitwise_and_output)
);