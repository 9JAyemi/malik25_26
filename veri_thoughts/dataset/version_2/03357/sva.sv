module bin_to_seven_seg_sva (
    input logic clk,
    input logic [6:0] S,
    input logic [3:0] D
);

    // D=0 must decode to the active-low seven-segment pattern for 0.
    check_decode_0: assert property (
        @(posedge clk) (D == 4'h0) |-> (S == 7'b0000001)
    );

    // D=1 must decode to the active-low seven-segment pattern for 1.
    check_decode_1: assert property (
        @(posedge clk) (D == 4'h1) |-> (S == 7'b1001111)
    );

    // D=2 must decode to the active-low seven-segment pattern for 2.
    check_decode_2: assert property (
        @(posedge clk) (D == 4'h2) |-> (S == 7'b0010010)
    );

    // D=3 must decode to the active-low seven-segment pattern for 3.
    check_decode_3: assert property (
        @(posedge clk) (D == 4'h3) |-> (S == 7'b0000110)
    );

    // D=4 must decode to the active-low seven-segment pattern for 4.
    check_decode_4: assert property (
        @(posedge clk) (D == 4'h4) |-> (S == 7'b1001100)
    );

    // D=5 must decode to the active-low seven-segment pattern for 5.
    check_decode_5: assert property (
        @(posedge clk) (D == 4'h5) |-> (S == 7'b0100100)
    );

    // D=6 must decode to the active-low seven-segment pattern for 6.
    check_decode_6: assert property (
        @(posedge clk) (D == 4'h6) |-> (S == 7'b0100000)
    );

    // D=7 must decode to the active-low seven-segment pattern for 7.
    check_decode_7: assert property (
        @(posedge clk) (D == 4'h7) |-> (S == 7'b0001111)
    );

    // D=8 must decode to the active-low seven-segment pattern for 8.
    check_decode_8: assert property (
        @(posedge clk) (D == 4'h8) |-> (S == 7'b0000000)
    );

    // D=9 must decode to the active-low seven-segment pattern for 9.
    check_decode_9: assert property (
        @(posedge clk) (D == 4'h9) |-> (S == 7'b0000100)
    );

    // D=A must decode to the active-low seven-segment pattern for A.
    check_decode_a: assert property (
        @(posedge clk) (D == 4'hA) |-> (S == 7'b0001000)
    );

    // D=B must decode to the active-low seven-segment pattern for B.
    check_decode_b: assert property (
        @(posedge clk) (D == 4'hB) |-> (S == 7'b1100000)
    );

    // D=C must decode to the active-low seven-segment pattern for C.
    check_decode_c: assert property (
        @(posedge clk) (D == 4'hC) |-> (S == 7'b0110001)
    );

    // D=D must decode to the active-low seven-segment pattern for D.
    check_decode_d: assert property (
        @(posedge clk) (D == 4'hD) |-> (S == 7'b1000010)
    );

    // D=E must decode to the active-low seven-segment pattern for E.
    check_decode_e: assert property (
        @(posedge clk) (D == 4'hE) |-> (S == 7'b0110000)
    );

    // D=F must decode to the active-low seven-segment pattern for F.
    check_decode_f: assert property (
        @(posedge clk) (D == 4'hF) |-> (S == 7'b0111000)
    );

endmodule