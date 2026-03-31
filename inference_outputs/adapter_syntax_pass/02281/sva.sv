module mux_priority_encoder_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic [7:0] in,
    input logic [2:0] pos,
    input logic [3:0] out_sum
);

    // pos must match the implemented priority-encoder selection.
    check_pos_priority_encoding: assert property (
        @(posedge clk)
        pos == ((in[7]) ? 3'd7 :
                (in[6]) ? 3'd6 :
                (in[5]) ? 3'd5 :
                (in[4]) ? 3'd4 :
                (in[3]) ? 3'd3 :
                (in[2]) ? 3'd2 :
                (in[1]) ? 3'd1 :
                (in[0]) ? 3'd0 :
                           3'd0)
    );

    // pos must always be one of the implemented encoder outputs.
    check_pos_legal_values: assert property (
        @(posedge clk)
        (pos == 3'd0) ||
        (pos == 3'd1) ||
        (pos == 3'd2) ||
        (pos == 3'd3) ||
        (pos == 3'd4) ||
        (pos == 3'd5) ||
        (pos == 3'd6) ||
        (pos == 3'd7)
    );

    // out_sum must match the muxed input plus the selected position.
    check_out_sum_function: assert property (
        @(posedge clk)
        out_sum == ((sel_b1 & sel_b2) ? (b ? (3'd1 + pos) : pos) :
                    ((sel_b1 | sel_b2) ? (a ? (3'd1 + pos) : pos) : pos))
    );

    // With both select bits low, the mux output is zero and out_sum is pos.
    check_out_sum_when_mux_zero: assert property (
        @(posedge clk)
        !(sel_b1 | sel_b2) |-> (out_sum == pos)
    );

    // With both select bits high, the mux output is b and out_sum is b + pos.
    check_out_sum_when_mux_b: assert property (
        @(posedge clk)
        (sel_b1 & sel_b2) |-> (out_sum == (b ? (3'd1 + pos) : pos))
    );

    // With only sel_b1 high, the mux output is a and out_sum is a + pos.
    check_out_sum_when_mux_a: assert property (
        @(posedge clk)
        (sel_b1 & !sel_b2) |-> (out_sum == (a ? (3'd1 + pos) : pos))
    );

    // With only sel_b2 high, the mux output is a and out_sum is a + pos.
    check_out_sum_when_mux_a_when_b1_low: assert property (
        @(posedge clk)
        (!sel_b1 & sel_b2) |-> (out_sum == (a ? (3'd1 + pos) : pos))
    );

endmodule