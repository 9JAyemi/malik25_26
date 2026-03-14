module alt_priority_encoder_sva (
    input  logic        clk,
    input  logic [7:0]  data,
    input  logic [2:0]  q
);
    // Local encoder matching priority_encoder_4bit behavior
    function automatic logic [1:0] enc4(input logic [3:0] d);
        case (d)
            4'b0001: enc4 = 2'b00;
            4'b0010: enc4 = 2'b01;
            4'b0100: enc4 = 2'b10;
            4'b1000: enc4 = 2'b11;
            default: enc4 = 2'b00;
        endcase
    endfunction

    // q[2] reflects whether ms_nibble[3:2] are both 1.
    check_q2_matches_ms_top2: assert property (
        @(posedge clk) disable iff (1'b0) q[2] == (data[7] & data[6])
    );

    // When ms_nibble is 0000, q is 000.
    check_ms_zero_forces_zero: assert property (
        @(posedge clk) disable iff (1'b0) (data[7:4] == 4'b0000) |-> (q == 3'b000)
    );

    // When ms_nibble is 1111, q is 111.
    check_ms_allones_forces_ones: assert property (
        @(posedge clk) disable iff (1'b0) (data[7:4] == 4'b1111) |-> (q == 3'b111)
    );

    // For ms_nibble 1110, q = {1, enc(ls_nibble)}.
    check_ms_1110_mapping: assert property (
        @(posedge clk) disable iff (1'b0) (data[7:4] == 4'b1110) |-> (q == {1'b1, enc4(data[3:0])})
    );

    // For ms_nibble 1101, q = {1, enc(ls_nibble)+1}.
    check_ms_1101_mapping: assert property (
        @(posedge clk) disable iff (1'b0) (data[7:4] == 4'b1101) |-> (q == {1'b1, enc4(data[3:0]) + 2'b01})
    );

    // For ms_nibble 1100, q = {1, enc(ls_nibble)+2}.
    check_ms_1100_mapping: assert property (
        @(posedge clk) disable iff (1'b0) (data[7:4] == 4'b1100) |-> (q == {1'b1, enc4(data[3:0]) + 2'b10})
    );

    // For other ms_nibble values, q = {0, enc(ls_nibble)}.
    check_default_mapping: assert property (
        @(posedge clk) disable iff (1'b0)
            ((data[7:4] != 4'b0000) && (data[7:4] != 4'b1111) &&
             (data[7:4] != 4'b1110) && (data[7:4] != 4'b1101) &&
             (data[7:4] != 4'b1100))
            |-> (q == {1'b0, enc4(data[3:0])})
    );

    // With ms=1101 and ls=1000, addition wraps to 00 -> q=100.
    check_wrap_ms1101_ls1000: assert property (
        @(posedge clk) disable iff (1'b0) (data[7:4] == 4'b1101 && data[3:0] == 4'b1000) |-> (q == 3'b100)
    );

    // With ms=1100 and ls=1000, addition wraps to 01 -> q=101.
    check_wrap_ms1100_ls1000: assert property (
        @(posedge clk) disable iff (1'b0) (data[7:4] == 4'b1100 && data[3:0] == 4'b1000) |-> (q == 3'b101)
    );

    // With ms=1100 and ls=0100, addition wraps to 00 -> q=100.
    check_wrap_ms1100_ls0100: assert property (
        @(posedge clk) disable iff (1'b0) (data[7:4] == 4'b1100 && data[3:0] == 4'b0100) |-> (q == 3'b100)
    );

    // With ms=1101 and ls=0100, addition yields 11 -> q=111.
    check_ms1101_ls0100_to_111: assert property (
        @(posedge clk) disable iff (1'b0) (data[7:4] == 4'b1101 && data[3:0] == 4'b0100) |-> (q == 3'b111)
    );
endmodule