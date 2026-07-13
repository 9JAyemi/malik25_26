module tail_length_sva (
    input  logic              clk,
    input  logic [3:0]        ir,
    input  logic [3:0]        len
);
    // len must equal the exact combinational function of ir.
    check_len_exact_mapping: assert property (
        @(posedge clk) len == {
            (ir == 4'b0011),
            (ir == 4'b0010),
            (ir == 4'b0001),
            ((ir | 4'b0101) == 4'b1101) | ((ir | 4'b1100) == 4'b1100)
        }
    );

    // len[3] is 1 iff ir == 4'b0011.
    check_len3_mapping: assert property (
        @(posedge clk) len[3] == (ir == 4'b0011)
    );

    // len[2] is 1 iff ir == 4'b0010.
    check_len2_mapping: assert property (
        @(posedge clk) len[2] == (ir == 4'b0010)
    );

    // len[1] is 1 iff ir == 4'b0001.
    check_len1_mapping: assert property (
        @(posedge clk) len[1] == (ir == 4'b0001)
    );

    // len[0] matches the OR-of-comparisons expression.
    check_len0_mapping: assert property (
        @(posedge clk) len[0] == ( ((ir | 4'b0101) == 4'b1101) | ((ir | 4'b1100) == 4'b1100) )
    );

    // len encoding is at most one-hot across all four bits.
    check_len_onehot0: assert property (
        @(posedge clk) $onehot0(len)
    );

    // If ir[1:0]==2'b00 then len[0] must be 1 (covers (ir|4'b1100)==4'b1100 case).
    check_len0_when_low10: assert property (
        @(posedge clk) ((ir[1] == 1'b0) && (ir[0] == 1'b0)) |-> (len[0] == 1'b1)
    );

    // If ir[3]==1 and ir[1]==0 then len[0] must be 1 (covers (ir|4'b0101)==4'b1101 case).
    check_len0_when_ir3_high_ir1_low: assert property (
        @(posedge clk) ((ir[3] == 1'b1) && (ir[1] == 1'b0)) |-> (len[0] == 1'b1)
    );

    // Specific mapping: ir==3 -> len==4'b1000; ir==2 -> 0100; ir==1 -> 0010.
    check_ir_eq_3_maps_to_len_1000: assert property (
        @(posedge clk) (ir == 4'b0011) |-> (len == 4'b1000)
    );
    check_ir_eq_2_maps_to_len_0100: assert property (
        @(posedge clk) (ir == 4'b0010) |-> (len == 4'b0100)
    );
    check_ir_eq_1_maps_to_len_0010: assert property (
        @(posedge clk) (ir == 4'b0001) |-> (len == 4'b0010)
    );

    // For ir in {0,4,8,9,12,13}, len must be 4'b0001.
    check_len0001_specific_ir: assert property (
        @(posedge clk)
            ((ir == 4'b0000) || (ir == 4'b0100) || (ir == 4'b1000) || (ir == 4'b1001) || (ir == 4'b1100) || (ir == 4'b1101))
            |-> (len == 4'b0001)
    );

    // For all other ir values, len must be 4'b0000.
    check_len0000_else: assert property (
        @(posedge clk)
            !((ir == 4'b0011) || (ir == 4'b0010) || (ir == 4'b0001) ||
              ((ir | 4'b0101) == 4'b1101) || ((ir | 4'b1100) == 4'b1100))
            |-> (len == 4'b0000)
    );
endmodule