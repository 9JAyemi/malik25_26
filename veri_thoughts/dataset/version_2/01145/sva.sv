module priority_encoder_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] pos
);
    // 0001 maps to position 0.
    encode_in_0001_to_pos0: assert property (
        @(posedge clk) (in == 4'b0001) |-> (pos == 2'd0)
    );

    // 0010 maps to position 1.
    encode_in_0010_to_pos1: assert property (
        @(posedge clk) (in == 4'b0010) |-> (pos == 2'd1)
    );

    // 0100 maps to position 2.
    encode_in_0100_to_pos2: assert property (
        @(posedge clk) (in == 4'b0100) |-> (pos == 2'd2)
    );

    // 1000 maps to position 3.
    encode_in_1000_to_pos3: assert property (
        @(posedge clk) (in == 4'b1000) |-> (pos == 2'd3)
    );

    // Any non-listed input maps to 0 (default case).
    encode_default_to_pos0: assert property (
        @(posedge clk) (in != 4'b0001 && in != 4'b0010 && in != 4'b0100 && in != 4'b1000) |-> (pos == 2'd0)
    );

    // If pos is 1 then input must be 0010.
    reverse_pos1_implies_0010: assert property (
        @(posedge clk) (pos == 2'd1) |-> (in == 4'b0010)
    );

    // If pos is 2 then input must be 0100.
    reverse_pos2_implies_0100: assert property (
        @(posedge clk) (pos == 2'd2) |-> (in == 4'b0100)
    );

    // If pos is 3 then input must be 1000.
    reverse_pos3_implies_1000: assert property (
        @(posedge clk) (pos == 2'd3) |-> (in == 4'b1000)
    );

    // If pos is 0 then input cannot be 0010/0100/1000.
    reverse_pos0_excludes_1_2_3: assert property (
        @(posedge clk) (pos == 2'd0) |-> (in != 4'b0010 && in != 4'b0100 && in != 4'b1000)
    );
endmodule