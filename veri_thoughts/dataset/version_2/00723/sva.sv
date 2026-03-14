module bin_to_two_bit_sva (
    input logic CLK,
    input logic [3:0] in,
    input logic [1:0] out
);
    // out[0] equals in[1] OR in[3].
    check_out0_mapping: assert property (
        @(posedge CLK) disable iff (1'b0) out[0] == (in[1] | in[3])
    );

    // out[1] equals in[2] OR in[3].
    check_out1_mapping: assert property (
        @(posedge CLK) disable iff (1'b0) out[1] == (in[2] | in[3])
    );

    // out equals {in[2]|in[3], in[1]|in[3]}.
    check_out_vector_mapping: assert property (
        @(posedge CLK) disable iff (1'b0) out == { (in[2] | in[3]), (in[1] | in[3]) }
    );

    // If in[3] is 1, out must be 2'b11.
    check_in3_forces_all_ones: assert property (
        @(posedge CLK) disable iff (1'b0) in[3] |-> (out == 2'b11)
    );

    // If in[3] is 0, out passes through in[2:1] to {out[1],out[0]}.
    check_in3_zero_pass_through: assert property (
        @(posedge CLK) disable iff (1'b0) !in[3] |-> ((out[0] == in[1]) && (out[1] == in[2]))
    );

    // If in[1]==0 and in[3]==0 then out[0]==0.
    check_out0_zero_conditions: assert property (
        @(posedge CLK) disable iff (1'b0) (!in[1] && !in[3]) |-> (out[0] == 1'b0)
    );

    // If in[2]==0 and in[3]==0 then out[1]==0.
    check_out1_zero_conditions: assert property (
        @(posedge CLK) disable iff (1'b0) (!in[2] && !in[3]) |-> (out[1] == 1'b0)
    );

    // All-zero input produces all-zero output.
    check_zero_input_zero_output: assert property (
        @(posedge CLK) disable iff (1'b0) (in == 4'b0000) |-> (out == 2'b00)
    );

    // With in[3]==0, in[1]==1 sets out[0].
    check_out0_set_by_in1_when_in3_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (in[1] && !in[3]) |-> (out[0] == 1'b1)
    );

    // With in[3]==0, in[2]==1 sets out[1].
    check_out1_set_by_in2_when_in3_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (in[2] && !in[3]) |-> (out[1] == 1'b1)
    );
endmodule