module priority_encoder_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] pos
);

    // Exact implemented mapping from in to pos.
    check_pos_matches_implemented_logic: assert property (
        @(posedge clk) pos == (((!in[3]) && in[2]) ? 2'b01 : 2'b00)
    );

    // If in[3] is set, the output falls through to 00.
    check_in3_forces_pos00: assert property (
        @(posedge clk) in[3] |-> (pos == 2'b00)
    );

    // If in[2] is the highest active bit, the output is 01.
    check_in2_maps_to_pos01: assert property (
        @(posedge clk) (!in[3] && in[2]) |-> (pos == 2'b01)
    );

    // If in[1] is the highest active bit, the output is 00.
    check_in1_maps_to_pos00: assert property (
        @(posedge clk) (!in[3] && !in[2] && in[1]) |-> (pos == 2'b00)
    );

    // If only in[0] can be selected, the output is 00.
    check_in0_maps_to_pos00: assert property (
        @(posedge clk) (!in[3] && !in[2] && !in[1] && in[0]) |-> (pos == 2'b00)
    );

    // With no asserted inputs, the output defaults to 00.
    check_no_input_defaults_to_pos00: assert property (
        @(posedge clk) (in == 4'b0000) |-> (pos == 2'b00)
    );

    // The implemented logic never produces 10 or 11.
    check_pos_is_limited_to_00_or_01: assert property (
        @(posedge clk) ((pos == 2'b00) || (pos == 2'b01))
    );

    // Output 01 can only come from bit 2 winning the chain.
    check_pos01_has_unique_cause: assert property (
        @(posedge clk) (pos == 2'b01) |-> (!in[3] && in[2])
    );

endmodule