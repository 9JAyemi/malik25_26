module halves_sum_sva (
    input logic [31:0] in,
    input logic [15:0] out
);
    // No clock or reset in RTL; pure combinational: out = (in[31:16] + in[15:0]) truncated to 16 bits.

    always_comb begin
        // out equals the 16-bit sum of upper and lower halves (truncated).
        check_out_eq_halves_sum: assert (out == (in[31:16] + in[15:0]));
        // If upper half is zero, out equals lower half.
        check_upper_zero_passthrough: assert ((in[31:16] != 16'h0000) || (out == in[15:0]));
        // If lower half is zero, out equals upper half.
        check_lower_zero_passthrough: assert ((in[15:0] != 16'h0000) || (out == in[31:16]));
        // When both halves are 0xFFFF, sum truncates to 0xFFFE.
        check_overflow_fffe: assert (!((in[31:16] == 16'hFFFF) && (in[15:0] == 16'hFFFF)) || (out == 16'hFFFE));
        // When upper is 0x0001 and lower is 0xFFFF, sum wraps to 0x0000.
        check_wrap_zero_example: assert (!((in[31:16] == 16'h0001) && (in[15:0] == 16'hFFFF)) || (out == 16'h0000));
    end
endmodule