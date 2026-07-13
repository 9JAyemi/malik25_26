module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic sub,
    input logic [3:0] I,
    input logic enable,
    input logic [3:0] q,
    input logic [3:0] add_sub_result,
    input logic [1:0] priority_encoder_D
);

    // Reset clears the registered add/sub result.
    check_reset_clears_add_sub_result: assert property (
        @(posedge clk) !reset |-> (add_sub_result == 4'b0000)
    );

    // Reset forces the top-level output low.
    check_reset_forces_q_low: assert property (
        @(posedge clk) !reset |-> (q == 4'b0000)
    );

    // The upper priority_encoder bit always reflects I[3].
    check_priority_encoder_bit1_follows_i3: assert property (
        @(posedge clk) disable iff (!reset)
        (priority_encoder_D[1] == I[3])
    );

    // With enable high, the lower priority_encoder bit uses I[2].
    check_priority_encoder_enable_high_path: assert property (
        @(posedge clk) disable iff (!reset)
        enable |-> (priority_encoder_D[0] == I[2])
    );

    // With enable low, the lower priority_encoder bit uses I[0].
    check_priority_encoder_enable_low_path: assert property (
        @(posedge clk) disable iff (!reset)
        !enable |-> (priority_encoder_D[0] == I[0])
    );

    // The top output is the add/sub result ANDed with zero-extended encoder bits.
    check_functional_module_and_behavior: assert property (
        @(posedge clk) disable iff (!reset)
        (q == (add_sub_result & {2'b00, priority_encoder_D}))
    );

    // The upper two output bits are always zero after the width-mismatched AND.
    check_q_upper_bits_zero: assert property (
        @(posedge clk) disable iff (!reset)
        (q[3:2] == 2'b00)
    );

    // Output bit 1 is add_sub_result[1] gated by I[3].
    check_q_bit1_behavior: assert property (
        @(posedge clk) disable iff (!reset)
        (q[1] == (add_sub_result[1] & I[3]))
    );

    // With enable high, output bit 0 is gated by I[2].
    check_q_bit0_enable_high_path: assert property (
        @(posedge clk) disable iff (!reset)
        enable |-> (q[0] == (add_sub_result[0] & I[2]))
    );

    // With enable low, output bit 0 is gated by I[0].
    check_q_bit0_enable_low_path: assert property (
        @(posedge clk) disable iff (!reset)
        !enable |-> (q[0] == (add_sub_result[0] & I[0]))
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (
    .clk(clk),
    .reset(reset),
    .A(A),
    .B(B),
    .sub(sub),
    .I(I),
    .enable(enable),
    .q(q),
    .add_sub_result(add_sub_result),
    .priority_encoder_D(priority_encoder_D)
);