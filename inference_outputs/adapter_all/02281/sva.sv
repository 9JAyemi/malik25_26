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

    // pos must match the implemented priority encoder.
    check_pos_priority_encoding: assert property (
        @(posedge clk)
        pos == (in[7] ? 3'd7 :
                in[6] ? 3'd6 :
                in[5] ? 3'd5 :
                in[4] ? 3'd4 :
                in[3] ? 3'd3 :
                in[2] ? 3'd2 :
                in[1] ? 3'd1 :
                in[0] ? 3'd0 :
                        3'd0)
    );

    // out_sum must match the muxed input plus the selected position.
    check_out_sum_function: assert property (
        @(posedge clk)
        out_sum == ((sel_b1 & sel_b2) ? b :
                    ((sel_b1 | sel_b2) ? a : 1'b0)) + pos
    );

    // With both select bits high, b is used and out_sum is b plus the position.
    check_b_selected: assert property (
        @(posedge clk)
        (sel_b1 & sel_b2) |-> (out_sum == b + pos)
    );

    // With either select bit high, a is used and out_sum is a plus the position.
    check_a_selected: assert property (
        @(posedge clk)
        (sel_b1 | sel_b2) |-> (out_sum == a + pos)
    );

    // With both select bits low, a is used and out_sum is a plus the position.
    check_a_selected_when_b_not_selected: assert property (
        @(posedge clk)
        !(sel_b1 & sel_b2) |-> (out_sum == a + pos)
    );

    // With no input bits set, the position is zero and out_sum is the selected input plus zero.
    check_zero_input_case: assert property (
        @(posedge clk)
        (in == 8'h00) |-> (pos == 3'd0) && (out_sum == ((sel_b1 & sel_b2) ? b : ((sel_b1 | sel_b2) ? a : 1'b0)))
    );

    // With only in[0] set, the position is zero and out_sum is the selected input plus zero.
    check_only_in0_case: assert property (
        @(posedge clk)
        (in == 8'h01) |-> (pos == 3'd0) && (out_sum == ((sel_b1 & sel_b2) ? b : ((sel_b1 | sel_b2) ? a : 1'b0)))
    );

    // With only in[1] set, the position is one and out_sum is the selected input plus one.
    check_only_in1_case: assert property (
        @(posedge clk)
        (in == 8'h02) |-> (pos == 3'd1) && (out_sum == ((sel_b1 & sel_b2) ? b : ((sel_b1 | sel_b2) ? a : 1'b0)) + 1'b1)
    );

    // With only in[2] set, the position is two and out_sum is the selected input plus two.
    check_only_in2_case: assert property (
        @(posedge clk)
        (in == 8'h04) |-> (pos == 3'd2) && (out_sum == ((sel_b1 & sel_b2) ? b : ((sel_b1 | sel_b2) ? a : 1'b0)) + 2'b10)
    );

    // With only in[3] set, the position is three and out_sum is the selected input plus three.
    check_only_in3_case: assert property (
        @(posedge clk)
        (in == 8'h08) |-> (pos == 3'd3) && (out_sum == ((sel_b1 & sel_b2) ? b : ((sel_b1 | sel_b2) ? a : 1'b0)) + 2'b11)
    );

    // With only in[4] set, the position is four and out_sum is the selected input plus four.
    check_only_in4_case: assert property (
        @(posedge clk)
        (in == 8'h10) |-> (pos == 3'd4) && (out_sum == ((sel_b1 & sel_b2) ? b : ((sel_b1 | sel_b2) ? a : 1'b0)) + 3'b100)
    );

    // With only in[5] set, the position is five and out_sum is the selected input plus five.
    check_only_in5_case: assert property (
        @(posedge clk)
        (in == 8'h20) |-> (pos == 3'd5) && (out_sum == ((sel_b1 & sel_b2) ? b : ((sel_b1 | sel_b2) ? a : 1'b0)) + 3'b101)
    );

    // With only in[6] set, the position is six and out_sum is the selected input plus six.
    check_only_in6_case: assert property (
        @(posedge clk)
        (in == 8'h40) |-> (pos == 3'd6) && (out_sum == ((sel_b1 & sel_b2) ? b : ((sel_b1 | sel_b2) ? a : 1'b0)) + 3'b110)
    );

    // With only in[7] set, the position is seven and out_sum is the selected input plus seven.
    check_only_in7_case: assert property (
        @(posedge clk)
        (in == 8'h80) |-> (pos == 3'd7) && (out_sum == ((sel_b1 & sel_b2) ? b : ((sel_b1 | sel_b2) ? a : 1'b0)) + 3'b111)
    );

endmodule