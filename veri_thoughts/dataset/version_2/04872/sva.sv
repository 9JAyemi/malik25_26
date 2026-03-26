module priority_encoder_sva (
    input logic clk,
    input logic [3:0] I,
    input logic [15:0] O
);

    // Input 0 selects output bit 0.
    check_decode_i0: assert property (
        @(posedge clk) (I == 4'h0) |-> (O == 16'b0000000000000001)
    );

    // Input 1 selects output bit 1.
    check_decode_i1: assert property (
        @(posedge clk) (I == 4'h1) |-> (O == 16'b0000000000000010)
    );

    // Input 2 selects output bit 2.
    check_decode_i2: assert property (
        @(posedge clk) (I == 4'h2) |-> (O == 16'b0000000000000100)
    );

    // Input 3 selects output bit 3.
    check_decode_i3: assert property (
        @(posedge clk) (I == 4'h3) |-> (O == 16'b0000000000001000)
    );

    // Input 4 selects output bit 4.
    check_decode_i4: assert property (
        @(posedge clk) (I == 4'h4) |-> (O == 16'b0000000000010000)
    );

    // Input 5 selects output bit 5.
    check_decode_i5: assert property (
        @(posedge clk) (I == 4'h5) |-> (O == 16'b0000000000100000)
    );

    // Input 6 selects output bit 6.
    check_decode_i6: assert property (
        @(posedge clk) (I == 4'h6) |-> (O == 16'b0000000001000000)
    );

    // Input 7 selects output bit 7.
    check_decode_i7: assert property (
        @(posedge clk) (I == 4'h7) |-> (O == 16'b0000000010000000)
    );

    // Input 8 selects output bit 8.
    check_decode_i8: assert property (
        @(posedge clk) (I == 4'h8) |-> (O == 16'b0000000100000000)
    );

    // Input 9 selects output bit 9.
    check_decode_i9: assert property (
        @(posedge clk) (I == 4'h9) |-> (O == 16'b0000001000000000)
    );

    // Input A selects output bit 10.
    check_decode_ia: assert property (
        @(posedge clk) (I == 4'ha) |-> (O == 16'b0000010000000000)
    );

    // Input B selects output bit 11.
    check_decode_ib: assert property (
        @(posedge clk) (I == 4'hb) |-> (O == 16'b0000100000000000)
    );

    // Input C selects output bit 12.
    check_decode_ic: assert property (
        @(posedge clk) (I == 4'hc) |-> (O == 16'b0001000000000000)
    );

    // Input D selects output bit 13.
    check_decode_id: assert property (
        @(posedge clk) (I == 4'hd) |-> (O == 16'b0010000000000000)
    );

    // Input E selects output bit 14.
    check_decode_ie: assert property (
        @(posedge clk) (I == 4'he) |-> (O == 16'b0100000000000000)
    );

    // Input F selects output bit 15.
    check_decode_if: assert property (
        @(posedge clk) (I == 4'hf) |-> (O == 16'b1000000000000000)
    );

    // Output always has exactly one bit asserted.
    check_output_onehot: assert property (
        @(posedge clk) $onehot(O)
    );

endmodule