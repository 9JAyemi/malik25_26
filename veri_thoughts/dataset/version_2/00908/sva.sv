module match_sva (
    input  logic        clk,
    input  logic [15:0] vec_i,
    input  logic        b8_i,
    input  logic        b12_i,
    input  logic        match1_o,
    input  logic        match2_o
);
    // match1_o equals the defined conjunction of selected bits and inputs.
    check_match1_definition: assert property (
        @(posedge clk) match1_o == ((vec_i[15:14] == 2'b00) && (vec_i[11] == 1'b0) && (vec_i[7] == b8_i) && (vec_i[3] == b12_i))
    );
    // match2_o equals the defined conjunction of selected bits and inputs.
    check_match2_definition: assert property (
        @(posedge clk) match2_o == ((vec_i[15:14] == 2'b00) && (vec_i[7] == b8_i) && (vec_i[3] == b12_i) && (vec_i[11] == 1'b0))
    );
    // The two outputs are always identical.
    check_outputs_equivalent: assert property (
        @(posedge clk) (match1_o == match2_o)
    );
    // If match1_o is HIGH, the required conditions hold.
    check_match1_high_requires_conditions: assert property (
        @(posedge clk) match1_o |-> ((vec_i[15:14] == 2'b00) && (vec_i[11] == 1'b0) && (vec_i[7] == b8_i) && (vec_i[3] == b12_i))
    );
    // If match2_o is HIGH, the required conditions hold.
    check_match2_high_requires_conditions: assert property (
        @(posedge clk) match2_o |-> ((vec_i[15:14] == 2'b00) && (vec_i[7] == b8_i) && (vec_i[3] == b12_i) && (vec_i[11] == 1'b0))
    );
    // When all conditions hold, both outputs are HIGH.
    check_conditions_imply_both_high: assert property (
        @(posedge clk) ((vec_i[15:14] == 2'b00) && (vec_i[11] == 1'b0) && (vec_i[7] == b8_i) && (vec_i[3] == b12_i)) |-> (match1_o && match2_o)
    );
    // Outputs remain stable if all inputs are stable.
    check_stable_when_all_inputs_stable: assert property (
        @(posedge clk) $stable({vec_i, b8_i, b12_i}) |-> $stable({match1_o, match2_o})
    );
    // Outputs depend only on vec_i[15:14], vec_i[11], vec_i[7], vec_i[3], b8_i, and b12_i.
    check_stable_when_relevant_subset_stable: assert property (
        @(posedge clk) $stable({vec_i[15:14], vec_i[11], vec_i[7], vec_i[3], b8_i, b12_i}) |-> $stable({match1_o, match2_o})
    );
    // If vec_i[15:14] != 2'b00, both outputs are LOW.
    check_vec15_14_zero_required: assert property (
        @(posedge clk) (vec_i[15:14] != 2'b00) |-> (!match1_o && !match2_o)
    );
    // If vec_i[11] != 0, both outputs are LOW.
    check_vec11_zero_required: assert property (
        @(posedge clk) (vec_i[11] != 1'b0) |-> (!match1_o && !match2_o)
    );
    // If b8_i mismatches vec_i[7], both outputs are LOW.
    check_b8_match_required: assert property (
        @(posedge clk) (vec_i[7] != b8_i) |-> (!match1_o && !match2_o)
    );
    // If b12_i mismatches vec_i[3], both outputs are LOW.
    check_b12_match_required: assert property (
        @(posedge clk) (vec_i[3] != b12_i) |-> (!match1_o && !match2_o)
    );
endmodule