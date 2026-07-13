module hexdisp_sva #(
    parameter int HEX_DIGITS = 8,
    parameter int SEGS_PER_DIGIT = 7
) (
    input logic clk,
    input logic [(HEX_DIGITS * 4 - 1):0] inword,
    input logic [(HEX_DIGITS * SEGS_PER_DIGIT - 1):0] outword
);

    function automatic [SEGS_PER_DIGIT-1:0] expected_sseg(input logic [3:0] nibble);
        unique case (nibble)
            4'h0: expected_sseg = ~7'b1111110;
            4'h1: expected_sseg = ~7'b0110000;
            4'h2: expected_sseg = ~7'b1101101;
            4'h3: expected_sseg = ~7'b1111001;
            4'h4: expected_sseg = ~7'b0110011;
            4'h5: expected_sseg = ~7'b1011011;
            4'h6: expected_sseg = ~7'b1011111;
            4'h7: expected_sseg = ~7'b1110000;
            4'h8: expected_sseg = ~7'b1111111;
            4'h9: expected_sseg = ~7'b1111011;
            4'hA: expected_sseg = ~7'b1110111;
            4'hB: expected_sseg = ~7'b0011111;
            4'hC: expected_sseg = ~7'b1001110;
            4'hD: expected_sseg = ~7'b0111101;
            4'hE: expected_sseg = ~7'b1001111;
            4'hF: expected_sseg = ~7'b1000111;
        endcase
    endfunction

    generate
        genvar i;
        for (i = 0; i < HEX_DIGITS; i = i + 1) begin : gen_digit_checks
            // Each output digit must encode its corresponding input nibble.
            check_digit_encoding: assert property (
                @(posedge clk)
                outword[(SEGS_PER_DIGIT * i) +: SEGS_PER_DIGIT] == expected_sseg(inword[(4 * i) +: 4])
            );
        end
    endgenerate

    // A stable input word must keep the full display output stable.
    check_word_stability: assert property (
        @(posedge clk)
        $stable(inword) |-> $stable(outword)
    );

    // The display output can only change when the input word changes.
    check_output_change_has_input_change: assert property (
        @(posedge clk)
        $changed(outword) |-> $changed(inword)
    );

endmodule