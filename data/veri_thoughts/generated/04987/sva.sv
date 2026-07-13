module bcd_to_7seg_sva #(parameter COUNT = 1) (
    input logic                  clk,
    input logic [COUNT*4 - 1:0]  bcd,
    input logic [COUNT - 1:0]    dot,
    input logic [COUNT*8 - 1:0]  out
);

    // External sampling clock for this combinational RTL; no reset exists in the DUT.
    function automatic logic [7:0] expected_out (
        input logic [3:0] bcd_digit,
        input logic       dot_bit
    );
        begin
            case (bcd_digit)
                4'b0000: expected_out = {7'b1111110, dot_bit};
                4'b0001: expected_out = {7'b0110000, dot_bit};
                4'b0010: expected_out = {7'b1101101, dot_bit};
                4'b0011: expected_out = {7'b1111001, dot_bit};
                4'b0100: expected_out = {7'b0110011, dot_bit};
                4'b0101: expected_out = {7'b1011011, dot_bit};
                4'b0110: expected_out = {7'b1011111, dot_bit};
                4'b0111: expected_out = {7'b1110000, dot_bit};
                4'b1000: expected_out = {7'b1111111, dot_bit};
                4'b1001: expected_out = {7'b1111011, dot_bit};
                default: expected_out = {7'b0000000, dot_bit};
            endcase
        end
    endfunction

    genvar i;
    generate
        for (i = 0; i < COUNT; i = i + 1) begin : gen_assert
            // Each digit byte matches the implemented BCD-to-7seg lookup.
            check_digit_encoding: assert property (
                @(posedge clk)
                out[(i + 1) * 8 - 1 : i * 8] ==
                expected_out(bcd[(i + 1) * 4 - 1 : i * 4], dot[i])
            );

            // The dot input drives the LSB of the corresponding output byte.
            check_dot_passthrough: assert property (
                @(posedge clk)
                out[i * 8] == dot[i]
            );

            // Invalid BCD values blank the segments and preserve the dot bit.
            check_invalid_digit_blank: assert property (
                @(posedge clk)
                (bcd[(i + 1) * 4 - 1 : i * 4] == 4'ha ||
                 bcd[(i + 1) * 4 - 1 : i * 4] == 4'hb ||
                 bcd[(i + 1) * 4 - 1 : i * 4] == 4'hc ||
                 bcd[(i + 1) * 4 - 1 : i * 4] == 4'hd ||
                 bcd[(i + 1) * 4 - 1 : i * 4] == 4'he ||
                 bcd[(i + 1) * 4 - 1 : i * 4] == 4'hf)
                |-> out[(i + 1) * 8 - 1 : i * 8] == {7'b0000000, dot[i]}
            );
        end
    endgenerate

endmodule