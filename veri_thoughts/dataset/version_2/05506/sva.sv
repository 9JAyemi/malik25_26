module top_module_sva (
    input logic [3:0] in,
    input logic clk,
    input logic d,
    input logic [2:0] q,
    input logic [1:0] pos,
    input logic [0:0] out
);

    // pos[0] is high only when all encoder inputs are low.
    check_encoder_pos_lsb: assert property (
        @(posedge clk) pos[0] == ~(|in)
    );

    // pos[1] matches the implemented enc_out[1] truth table.
    check_encoder_pos_msb: assert property (
        @(posedge clk) pos[1] == (in[3] & ~(in[2] ^ in[1]))
    );

    // q[0] captures d from the previous clock edge.
    check_shift_reg_q0_updates: assert property (
        @(posedge clk) 1'b1 |=> (q[0] == $past(d))
    );

    // q[1] captures the previous value of q[0].
    check_shift_reg_q1_updates: assert property (
        @(posedge clk) 1'b1 |=> (q[1] == $past(q[0]))
    );

    // q[2] captures the previous value of q[1].
    check_shift_reg_q2_updates: assert property (
        @(posedge clk) 1'b1 |=> (q[2] == $past(q[1]))
    );

    // out is the XOR of q[2] and the encoder MSB.
    check_out_xor_function: assert property (
        @(posedge clk) out[0] == (q[2] ^ pos[1])
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (
    .in(in),
    .clk(clk),
    .d(d),
    .q(q),
    .pos(pos),
    .out(out)
);