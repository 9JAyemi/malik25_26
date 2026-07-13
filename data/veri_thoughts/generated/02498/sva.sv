module top_module_sva (
    input logic CLK,
    input logic [3:0] in,
    input logic [7:0] out
);

    // Helper: 4-bit two's complement of x
    function automatic logic [3:0] f_twos (input logic [3:0] x);
        f_twos = (~x) + 4'd1;
    endfunction

    // Helper: 4-bit BCD mapping as implemented in RTL
    function automatic logic [3:0] f_bcd (input logic [3:0] x);
        unique case (x)
            4'b0000: f_bcd = 4'b0000;
            4'b0001: f_bcd = 4'b0001;
            4'b0010: f_bcd = 4'b0010;
            4'b0011: f_bcd = 4'b0011;
            4'b0100: f_bcd = 4'b0100;
            4'b0101: f_bcd = 4'b0101;
            4'b0110: f_bcd = 4'b0110;
            4'b0111: f_bcd = 4'b0111;
            4'b1000: f_bcd = 4'b1000;
            4'b1001: f_bcd = 4'b1001;
            4'b1010: f_bcd = 4'b0001;
            4'b1011: f_bcd = 4'b0010;
            4'b1100: f_bcd = 4'b0011;
            4'b1101: f_bcd = 4'b0100;
            4'b1110: f_bcd = 4'b0101;
            4'b1111: f_bcd = 4'b0110;
            default: f_bcd = 4'b0000;
        endcase
    endfunction

    // Combined output matches concatenation of two's complement and BCD of in.
    check_combined_output: assert property (
        @(posedge CLK) out == { f_twos(in), f_bcd(in) }
    );

    // Upper nibble equals two's complement of in.
    check_twos_high_nibble: assert property (
        @(posedge CLK) out[7:4] == f_twos(in)
    );

    // Lower nibble equals BCD mapping of in.
    check_bcd_low_nibble: assert property (
        @(posedge CLK) out[3:0] == f_bcd(in)
    );

    // For in 0..9, BCD nibble equals in.
    check_bcd_small_digits: assert property (
        @(posedge CLK) (in <= 4'd9) |-> (out[3:0] == in)
    );

    // For in 10..15, BCD nibble equals in - 9.
    check_bcd_large_digits: assert property (
        @(posedge CLK) (in >= 4'd10) |-> (out[3:0] == (in - 4'd9))
    );

    // BCD nibble is always in range 0..9.
    check_bcd_digit_range: assert property (
        @(posedge CLK) out[3:0] <= 4'd9
    );

    // Input 0 produces 0x00 on out.
    check_zero_input_output_zero: assert property (
        @(posedge CLK) (in == 4'd0) |-> (out == 8'h00)
    );

    // Upper nibble zero only when in is zero.
    check_upper_zero_implies_input_zero: assert property (
        @(posedge CLK) (out[7:4] == 4'd0) |-> (in == 4'd0)
    );

    // If input is stable, output remains stable.
    check_output_stable_when_input_stable: assert property (
        @(posedge CLK) $stable(in) |-> $stable(out)
    );

    // Applying two's complement to upper nibble returns original in.
    check_twos_involution_via_out: assert property (
        @(posedge CLK) f_twos(out[7:4]) == in
    );

endmodule