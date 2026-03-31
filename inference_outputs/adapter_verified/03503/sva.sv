module jt51_mod_sva (
    input logic       clk,
    input logic       m1_enters,
    input logic       m2_enters,
    input logic       c1_enters,
    input logic       c2_enters,
    input logic [2:0] alg_I,
    input logic       use_prevprev1,
    input logic       use_internal_x,
    input logic       use_internal_y,
    input logic       use_prev2,
    input logic       use_prev1
);

// use_prevprev1 matches the RTL equation.
    check_use_prevprev1_equation: assert property (
        @(posedge clk)
        use_prevprev1 == (m1_enters | (m2_enters & alg_hot[5]))
    );

// use_prev2 matches the RTL equation.
    check_use_prev2_equation: assert property (
        @(posedge clk)
        use_prev2 == ((m2_enters & (~|alg_hot[2:0])) | (c2_enters & alg_hot[3]))
    );

// use_internal_x matches the RTL equation.
    check_use_internal_x_equation: assert property (
        @(posedge clk)
        use_internal_x == (c2_enters & alg_hot[2])
    );

// use_internal_y matches the RTL equation.
    check_use_internal_y_equation: assert property (
        @(posedge clk)
        use_internal_y == (c2_enters & (|{alg_hot[4:3], alg_hot[1:0]}))
    );

// use_prev1 matches the RTL equation.
    check_use_prev1_equation: assert property (
        @(posedge clk)
        use_prev1 == (m1_enters |
                       (m2_enters & alg_hot[1]) |
                       (c1_enters & (~|{alg_hot[6:3], alg_hot[0]})) |
                       (c2_enters & (~|{alg_hot[5], alg_hot[2]})))
    );

// alg_I=0 selects bit 0 and drives use_prevprev1 from m1 or m2&bit0.
    check_alg0_selects_bit0: assert property (
        @(posedge clk)
        (alg_I == 3'd0) |-> (use_prevprev1 == (m1_enters | (m2_enters & alg_hot[0])))
    );

// alg_I=1 selects bit 1 and drives use_prevprev1 from m1 or m2&bit1.
    check_alg1_selects_bit1: assert property (
        @(posedge clk)
        (alg_I == 3'd1) |-> (use_prevprev1 == (m1_enters | (m2_enters & alg_hot[1])))
    );

// alg_I=2 selects bit 2 and drives use_prevprev1 from m1 or m2&bit2.
    check_alg2_selects_bit2: assert property (
        @(posedge clk)
        (alg_I == 3'd2) |-> (use_prevprev1 == (m1_enters | (m2_enters & alg_hot[2])))
    );

// alg_I=3 selects bit 3 and drives use_prevprev1 from m1 or m2&bit3.
    check_alg3_selects_bit3: assert property (
        @(posedge clk)
        (alg_I == 3'd3) |-> (use_prevprev1 == (m1_enters | (m2_enters & alg_hot[3])))
    );

// alg_I=4 selects bit 4 and drives use_prevprev1 from m1 or m2&bit4.
    check_alg4_selects_bit4: assert property (
        @(posedge clk)
        (alg_I == 3'd4) |-> (use_prevprev1 == (m1_enters | (m2_enters & alg_hot[4])))
    );

// alg_I=5 selects bit 5 and drives use_prevprev1 from m1 or m2&bit5.
    check_alg5_selects_bit5: assert property (
        @(posedge clk)
        (alg_I == 3'd5) |-> (use_prevprev1 == (m1_enters | (m2_enters & alg_hot[5])))
    );

// alg_I=6 selects bit 6 and drives use_prevprev1 from m1 or m2&bit6.
    check_alg6_selects_bit6: assert property (
        @(posedge clk)
        (alg_I == 3'd6) |-> (use_prevprev1 == (m1_enters | (m2_enters & alg_hot[6])))
    );

// alg_I=7 selects bit 7 and drives use_prevprev1 from m1 or m2&bit7.
    check_alg7_selects_bit7: assert property (
        @(posedge clk)
        (alg_I == 3'd7) |-> (use_prevprev1 == (m1_enters | (m2_enters & alg_hot[7])))
    );

endmodule
