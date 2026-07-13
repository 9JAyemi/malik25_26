module Score_sva (
    input logic RESET,
    input logic [11:0] SCORE,
    input logic [6:0] DISP_SU,
    input logic [6:0] DISP_SD,
    input logic [6:0] DISP_SC,
    input logic [6:0] DISP_SM
);

    function automatic logic [6:0] sevenseg(input logic [3:0] digit);
        begin
            case (digit)
                4'd0: sevenseg = 7'b1111110;
                4'd1: sevenseg = 7'b0110000;
                4'd2: sevenseg = 7'b1101101;
                4'd3: sevenseg = 7'b1111001;
                4'd4: sevenseg = 7'b0110011;
                4'd5: sevenseg = 7'b1011011;
                4'd6: sevenseg = 7'b1011111;
                4'd7: sevenseg = 7'b1110000;
                4'd8: sevenseg = 7'b1111111;
                4'd9: sevenseg = 7'b1111011;
                default: sevenseg = 7'b0000000;
            endcase
        end
    endfunction

    function automatic logic [3:0] digit_m(input logic [11:0] s);
        int unsigned tmp;
        begin
            tmp = s;
            digit_m = tmp / 32'd1000;
        end
    endfunction

    function automatic logic [3:0] digit_c(input logic [11:0] s);
        int unsigned tmp;
        begin
            tmp = s;
            digit_c = (tmp % 32'd1000) / 32'd100;
        end
    endfunction

    function automatic logic [3:0] digit_d(input logic [11:0] s);
        int unsigned tmp;
        begin
            tmp = s;
            digit_d = (tmp % 32'd100) / 32'd10;
        end
    endfunction

    function automatic logic [3:0] digit_u(input logic [11:0] s);
        int unsigned tmp;
        begin
            tmp = s;
            digit_u = tmp % 32'd10;
        end
    endfunction

    // Reset forces all display outputs low.
    check_reset_blanks_all_displays: assert property (
        @($global_clock)
        RESET |-> (DISP_SU == 7'b0000000) &&
                  (DISP_SD == 7'b0000000) &&
                  (DISP_SC == 7'b0000000) &&
                  (DISP_SM == 7'b0000000)
    );

    // Thousands display decodes the thousands digit of SCORE.
    check_thousands_display_decode: assert property (
        @($global_clock) disable iff (RESET)
        DISP_SM == sevenseg(digit_m(SCORE))
    );

    // Hundreds display decodes the hundreds digit of SCORE.
    check_hundreds_display_decode: assert property (
        @($global_clock) disable iff (RESET)
        DISP_SC == sevenseg(digit_c(SCORE))
    );

    // Tens display decodes the tens digit of SCORE.
    check_tens_display_decode: assert property (
        @($global_clock) disable iff (RESET)
        DISP_SD == sevenseg(digit_d(SCORE))
    );

    // Units display decodes the ones digit of SCORE.
    check_units_display_decode: assert property (
        @($global_clock) disable iff (RESET)
        DISP_SU == sevenseg(digit_u(SCORE))
    );

    // Outside reset, the displays never use the blank default pattern.
    check_active_outputs_are_not_blank: assert property (
        @($global_clock) disable iff (RESET)
        (DISP_SU != 7'b0000000) &&
        (DISP_SD != 7'b0000000) &&
        (DISP_SC != 7'b0000000) &&
        (DISP_SM != 7'b0000000)
    );

    // A score of zero displays 0000 rather than blanking the digits.
    check_zero_score_shows_0000: assert property (
        @($global_clock) disable iff (RESET)
        (SCORE == 12'd0) |-> (DISP_SU == sevenseg(4'd0)) &&
                             (DISP_SD == sevenseg(4'd0)) &&
                             (DISP_SC == sevenseg(4'd0)) &&
                             (DISP_SM == sevenseg(4'd0))
    );

    // The maximum 12-bit score displays as 4095.
    check_max_score_shows_4095: assert property (
        @($global_clock) disable iff (RESET)
        (SCORE == 12'd4095) |-> (DISP_SM == sevenseg(4'd4)) &&
                                (DISP_SC == sevenseg(4'd0)) &&
                                (DISP_SD == sevenseg(4'd9)) &&
                                (DISP_SU == sevenseg(4'd5))
    );

endmodule