module functional_module_assertions (
    input logic        clk,
    input logic [3:0]  B,
    input logic [1:0]  in,
    input logic [15:0] out
);

    function automatic [3:0] expected_e(input logic [3:0] b);
        begin
            case (b)
                4'b0000: expected_e = 4'b0011;
                4'b0001: expected_e = 4'b0100;
                4'b0010: expected_e = 4'b0101;
                4'b0011: expected_e = 4'b0110;
                4'b0100: expected_e = 4'b0111;
                4'b0101: expected_e = 4'b1000;
                4'b0110: expected_e = 4'b1001;
                4'b0111: expected_e = 4'b1010;
                4'b1000: expected_e = 4'b1011;
                4'b1001: expected_e = 4'b1100;
                4'b1010: expected_e = 4'b1101;
                4'b1011: expected_e = 4'b1110;
                4'b1100: expected_e = 4'b1111;
                4'b1101: expected_e = 4'b0001;
                4'b1110: expected_e = 4'b0010;
                4'b1111: expected_e = 4'b0011;
                default: expected_e = 4'b0000;
            endcase
        end
    endfunction

    function automatic [15:0] expected_d(input logic [1:0] sel);
        begin
            case (sel)
                2'b00: expected_d = 16'b0000000000000001;
                2'b01: expected_d = 16'b0000000000000010;
                2'b10: expected_d = 16'b0000000000000100;
                2'b11: expected_d = 16'b0000000000001000;
                default: expected_d = 16'b0000000000000000;
            endcase
        end
    endfunction

    function automatic [15:0] expected_out(input logic [3:0] b, input logic [1:0] sel);
        begin
            expected_out = expected_d(sel) << expected_e(b);
        end
    endfunction

    // Full output matches the decoder output shifted by the excess-3 code.
    check_out_matches_function: assert property (
        @(posedge clk) out == expected_out(B, in)
    );

    // Output can only be one-hot or zero after shifting and truncation.
    check_out_onehot_or_zero: assert property (
        @(posedge clk) $onehot0(out)
    );

    // Decoder input 00 selects bit 0 before shifting.
    check_in_00_path: assert property (
        @(posedge clk) (in == 2'b00) |-> (out == (16'h0001 << expected_e(B)))
    );

    // Decoder input 01 selects bit 1 before shifting.
    check_in_01_path: assert property (
        @(posedge clk) (in == 2'b01) |-> (out == (16'h0002 << expected_e(B)))
    );

    // Decoder input 10 selects bit 2 before shifting.
    check_in_10_path: assert property (
        @(posedge clk) (in == 2'b10) |-> (out == (16'h0004 << expected_e(B)))
    );

    // Decoder input 11 selects bit 3 before shifting.
    check_in_11_path: assert property (
        @(posedge clk) (in == 2'b11) |-> (out == (16'h0008 << expected_e(B)))
    );

    // B=1100 maps to an excess-3 code of 15.
    check_b_1100_mapping: assert property (
        @(posedge clk) (B == 4'b1100) |-> (out == (expected_d(in) << 4'd15))
    );

    // B=1101 maps to a wrapped excess-3 code of 1.
    check_b_1101_mapping: assert property (
        @(posedge clk) (B == 4'b1101) |-> (out == (expected_d(in) << 4'd1))
    );

    // B=1110 maps to a wrapped excess-3 code of 2.
    check_b_1110_mapping: assert property (
        @(posedge clk) (B == 4'b1110) |-> (out == (expected_d(in) << 4'd2))
    );

    // B=1111 maps to an excess-3 code of 3.
    check_b_1111_mapping: assert property (
        @(posedge clk) (B == 4'b1111) |-> (out == (expected_d(in) << 4'd3))
    );

endmodule