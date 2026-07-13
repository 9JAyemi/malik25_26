module jt51_mod_sva (
    input logic m1_enters,
    input logic m2_enters,
    input logic c1_enters,
    input logic c2_enters,
    input logic [2:0] alg_I,
    output logic use_prevprev1,
    output logic use_internal_x,
    output logic use_internal_y,
    output logic use_prev2,
    output logic use_prev1
);
    // Sequential logic assertions

    // use_prevprev1 is set based on m1_enters, m2_enters, and alg_hot[5]
    use_prevprev1_seq: assert property (
        @(posedge clk) disable iff (!reset_n) use_prevprev1 |-> (m1_enters | (m2_enters & alg_hot[5]))
    );

    // use_prev2 is set based on m2_enters, alg_hot[2:0], and c2_enters & alg_hot[3]
    use_prev2_seq: assert property (
        @(posedge clk) disable iff (!reset_n) use_prev2 |-> ((m2_enters & (~alg_hot[2:0])) | (c2_enters & alg_hot[3]))
    );

    // use_internal_x is set based on c2_enters and alg_hot[2]
    use_internal_x_seq: assert property (
        @(posedge clk) disable iff (!reset_n) use_internal_x |-> (c2_enters & alg_hot[2])
    );

    // use_internal_y is set based on c2_enters and alg_hot[4:3] & alg_hot[1:0]
    use_internal_y_seq: assert property (
        @(posedge clk) disable iff (!reset_n) use_internal_y |-> (c2_enters & (|{alg_hot[4:3], alg_hot[1:0]}))
    );

    // use_prev1 is set based on m1_enters, m2_enters, alg_hot[1], c1_enters, and c2_enters
    use_prev1_seq: assert property (
        @(posedge clk) disable iff (!reset_n) use_prev1 |-> (m1_enters | (m2_enters & alg_hot[1]) |
            (c1_enters & (~{alg_hot[6:3], alg_hot[0]})) |
            (c2_enters & (~{alg_hot[5], alg_hot[2]})))
    );

    // Combinational logic assertions

    // alg_hot is set based on alg_I
    alg_hot_comb: assert property (
        @(posedge clk) disable iff (!reset_n) alg_hot |-> (case(alg_I)
            3'd0: 8'h1;  3'd1: 8'h2;  3'd2: 8'h4;  3'd3: 8'h8;  3'd4: 8'h10; 3'd5: 8'h20; 3'd6: 8'h40; 3'd7: 8'h80; default: 8'hx;
        endcase)
    );

endmodule