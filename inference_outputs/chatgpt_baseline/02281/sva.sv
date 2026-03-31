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
    // pos selects index of lowest-order '1' in in (bit 0 has highest priority).
    check_pos_priority_bit0: assert property (
        @(posedge clk) in[0] |-> (pos == 3'd0)
    );
    // pos==1 when in[1] is 1 and no lower bit is set.
    check_pos_priority_bit1: assert property (
        @(posedge clk) (in[1] && !in[0]) |-> (pos == 3'd1)
    );
    // pos==2 when in[2] is 1 and no lower bit is set.
    check_pos_priority_bit2: assert property (
        @(posedge clk) (in[2] && !in[1] && !in[0]) |-> (pos == 3'd2)
    );
    // pos==3 when in[3] is 1 and no lower bit is set.
    check_pos_priority_bit3: assert property (
        @(posedge clk) (in[3] && !in[2] && !in[1] && !in[0]) |-> (pos == 3'd3)
    );
    // pos==4 when in[4] is 1 and no lower bit is set.
    check_pos_priority_bit4: assert property (
        @(posedge clk) (in[4] && !in[3] && !in[2] && !in[1] && !in[0]) |-> (pos == 3'd4)
    );
    // pos==5 when in[5] is 1 and no lower bit is set.
    check_pos_priority_bit5: assert property (
        @(posedge clk) (in[5] && !in[4] && !in[3] && !in[2] && !in[1] && !in[0]) |-> (pos == 3'd5)
    );
    // pos==6 when in[6] is 1 and no lower bit is set.
    check_pos_priority_bit6: assert property (
        @(posedge clk) (in[6] && !in[5] && !in[4] && !in[3] && !in[2] && !in[1] && !in[0]) |-> (pos == 3'd6)
    );
    // pos==7 when in[7] is 1 and no lower bit is set.
    check_pos_priority_bit7: assert property (
        @(posedge clk) (in[7] && !in[6] && !in[5] && !in[4] && !in[3] && !in[2] && !in[1] && !in[0]) |-> (pos == 3'd7)
    );
    // When no bits are set, pos is 0.
    check_pos_when_none_set: assert property (
        @(posedge clk) (~|in) |-> (pos == 3'd0)
    );

    // out_sum equals pos plus the selected mux output (b if both sel=1, else a if any sel=1, else 0).
    check_out_sum_matches_equation: assert property (
        @(posedge clk)
        out_sum == ({1'b0, pos} + {3'b0, ((sel_b1 & sel_b2) ? b : ((sel_b1 | sel_b2) ? a : 1'b0))})
    );
    // When neither select is asserted, out_sum equals pos (mux_out=0).
    check_out_sum_sel00_no_add: assert property (
        @(posedge clk)
        (!sel_b1 && !sel_b2) |-> (out_sum == {1'b0, pos})
    );
    // When exactly one select is asserted, out_sum equals pos + a.
    check_out_sum_sel_one_add_a: assert property (
        @(posedge clk)
        (sel_b1 ^ sel_b2) |-> (out_sum == ({1'b0, pos} + {3'b0, a}))
    );
    // When both selects are asserted, out_sum equals pos + b.
    check_out_sum_sel11_add_b: assert property (
        @(posedge clk)
        (sel_b1 && sel_b2) |-> (out_sum == ({1'b0, pos} + {3'b0, b}))
    );
    // The MSB of out_sum is high only when selected mux output is 1 and pos==7.
    check_out_sum_msb_carry: assert property (
        @(posedge clk)
        out_sum[3] == ( ((sel_b1 & sel_b2) ? b : ((sel_b1 | sel_b2) ? a : 1'b0)) & (&pos) )
    );
endmodule