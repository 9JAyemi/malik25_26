module binary_to_excess3_sva (
    input logic       clk,
    input logic [3:0] B,
    input logic [3:0] E
);

    // Combinational DUT sampled on an external formal clock; no reset is present.

    // B=0 maps to E=3.
    check_map_0_to_3: assert property (
        @(posedge clk) (B == 4'h0) |-> (E == 4'h3)
    );

    // B=1 maps to E=4.
    check_map_1_to_4: assert property (
        @(posedge clk) (B == 4'h1) |-> (E == 4'h4)
    );

    // B=2 maps to E=5.
    check_map_2_to_5: assert property (
        @(posedge clk) (B == 4'h2) |-> (E == 4'h5)
    );

    // B=3 maps to E=6.
    check_map_3_to_6: assert property (
        @(posedge clk) (B == 4'h3) |-> (E == 4'h6)
    );

    // B=4 maps to E=7.
    check_map_4_to_7: assert property (
        @(posedge clk) (B == 4'h4) |-> (E == 4'h7)
    );

    // B=5 maps to E=8.
    check_map_5_to_8: assert property (
        @(posedge clk) (B == 4'h5) |-> (E == 4'h8)
    );

    // B=6 maps to E=9.
    check_map_6_to_9: assert property (
        @(posedge clk) (B == 4'h6) |-> (E == 4'h9)
    );

    // B=7 maps to E=10.
    check_map_7_to_a: assert property (
        @(posedge clk) (B == 4'h7) |-> (E == 4'hA)
    );

    // B=8 maps to E=11.
    check_map_8_to_b: assert property (
        @(posedge clk) (B == 4'h8) |-> (E == 4'hB)
    );

    // B=9 maps to E=12.
    check_map_9_to_c: assert property (
        @(posedge clk) (B == 4'h9) |-> (E == 4'hC)
    );

    // B=10 maps to E=13.
    check_map_a_to_d: assert property (
        @(posedge clk) (B == 4'hA) |-> (E == 4'hD)
    );

    // B=11 maps to E=14.
    check_map_b_to_e: assert property (
        @(posedge clk) (B == 4'hB) |-> (E == 4'hE)
    );

    // B=12 maps to E=15.
    check_map_c_to_f: assert property (
        @(posedge clk) (B == 4'hC) |-> (E == 4'hF)
    );

    // B=13 maps to E=0.
    check_map_d_to_0: assert property (
        @(posedge clk) (B == 4'hD) |-> (E == 4'h0)
    );

    // B=14 maps to E=1.
    check_map_e_to_1: assert property (
        @(posedge clk) (B == 4'hE) |-> (E == 4'h1)
    );

    // B=15 maps to E=2.
    check_map_f_to_2: assert property (
        @(posedge clk) (B == 4'hF) |-> (E == 4'h2)
    );

endmodule