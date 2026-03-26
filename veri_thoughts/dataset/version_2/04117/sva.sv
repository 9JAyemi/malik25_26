module binary_to_gray_sva (
    input logic [3:0] B,
    input logic       clk,
    input logic [3:0] G
);

    // Output matches the implemented two-stage registered prefix-XOR transform of B.
    check_output_vector_transform: assert property (
        @(posedge clk)
        1'b1 |-> ##2
        (G == {($past(B[3],2) ^ $past(B[2],2) ^ $past(B[1],2) ^ $past(B[0],2)),
               ($past(B[2],2) ^ $past(B[1],2) ^ $past(B[0],2)),
               ($past(B[1],2) ^ $past(B[0],2)),
               $past(B[0],2)})
    );

    // G[0] is B[0] delayed through the registered pipeline.
    check_g0_pipeline_mapping: assert property (
        @(posedge clk)
        1'b1 |-> ##2
        (G[0] == $past(B[0],2))
    );

    // G[1] is the prefix XOR of sampled B[1:0].
    check_g1_prefix_xor_mapping: assert property (
        @(posedge clk)
        1'b1 |-> ##2
        (G[1] == ($past(B[1],2) ^ $past(B[0],2)))
    );

    // G[2] is the prefix XOR of sampled B[2:0].
    check_g2_prefix_xor_mapping: assert property (
        @(posedge clk)
        1'b1 |-> ##2
        (G[2] == ($past(B[2],2) ^ $past(B[1],2) ^ $past(B[0],2)))
    );

    // G[3] is the prefix XOR of sampled B[3:0].
    check_g3_prefix_xor_mapping: assert property (
        @(posedge clk)
        1'b1 |-> ##2
        (G[3] == ($past(B[3],2) ^ $past(B[2],2) ^ $past(B[1],2) ^ $past(B[0],2)))
    );

endmodule