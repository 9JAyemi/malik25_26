module sseg_decode_sva #(
    parameter REG = 0,
    parameter INV = 1
)(
    input logic       clk,
    input logic       rst,
    input logic [3:0] num,
    input logic [6:0] sseg
);

    function automatic logic [6:0] decode_map(input logic [3:0] val);
        begin
            case (val)
                4'h0: decode_map = 7'b0111111;
                4'h1: decode_map = 7'b0000110;
                4'h2: decode_map = 7'b1011011;
                4'h3: decode_map = 7'b1001111;
                4'h4: decode_map = 7'b1100110;
                4'h5: decode_map = 7'b1101101;
                4'h6: decode_map = 7'b1111101;
                4'h7: decode_map = 7'b0000111;
                4'h8: decode_map = 7'b1111111;
                4'h9: decode_map = 7'b1101111;
                4'ha: decode_map = 7'b1110111;
                4'hb: decode_map = 7'b1111100;
                4'hc: decode_map = 7'b0111001;
                4'hd: decode_map = 7'b1011110;
                4'he: decode_map = 7'b1111001;
                4'hf: decode_map = 7'b1110001;
                default: decode_map = 7'b0000000;
            endcase
        end
    endfunction

    function automatic logic [6:0] expected_sseg(input logic [3:0] val);
        begin
            expected_sseg = INV ? ~decode_map(val) : decode_map(val);
        end
    endfunction

    generate
        if (REG == 0) begin : gen_comb_asserts
            // Unregistered output matches the current decoded value with optional inversion.
            check_comb_output_matches_decode: assert property (
                @(posedge clk) disable iff (rst)
                sseg == expected_sseg(num)
            );

            // A stable input keeps the unregistered output stable across clocks.
            check_comb_stable_input_keeps_output_stable: assert property (
                @(posedge clk) disable iff (rst)
                (!$initstate && $stable(num)) |-> $stable(sseg)
            );

            // A sampled input change produces a sampled output change.
            check_comb_input_change_updates_output: assert property (
                @(posedge clk) disable iff (rst)
                (!$initstate && $changed(num)) |-> $changed(sseg)
            );
        end else begin : gen_reg_asserts
            // While reset is asserted, the registered output is cleared.
            check_reg_reset_clears_output: assert property (
                @(posedge clk)
                rst |-> (sseg == 7'b0000000)
            );

            // The first sampled cycle after reset remains at the reset value.
            check_reg_first_cycle_after_reset_is_zero: assert property (
                @(posedge clk) disable iff (rst)
                (!$initstate && $past(rst)) |-> (sseg == 7'b0000000)
            );

            // Outside reset, the sampled output is either the reset value or the prior decoded value.
            check_reg_output_is_reset_or_prior_decode: assert property (
                @(posedge clk) disable iff (rst)
                (!$initstate && !$past(rst)) |-> ((sseg == 7'b0000000) || (sseg == expected_sseg($past(num))))
            );
        end
    endgenerate

endmodule