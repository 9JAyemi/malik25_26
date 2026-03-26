module shift_register_sva #(
    parameter integer DIN_N  = 256,
    parameter integer DOUT_N = 256
) (
    input logic clk,
    input logic stb,
    input logic di,
    input logic do,
    input logic [DIN_N-1:0]  din_shr,
    input logic [DOUT_N-1:0] dout_shr
);

    // do mirrors the MSB of dout_shr.
    check_do_matches_dout_msb: assert property (
        @(posedge clk) do == dout_shr[DOUT_N-1]
    );

    // stb shifts din_shr and loads di into bit 0.
    check_din_shifts_on_stb: assert property (
        @(posedge clk) stb |=> din_shr == (($past(din_shr) << 1) | $past(di))
    );

    // Without stb, din_shr holds its value.
    check_din_holds_without_stb: assert property (
        @(posedge clk) !stb |=> din_shr == $past(din_shr)
    );

    // dout_shr shifts every cycle and loads din_shr's prior MSB into bit 0.
    check_dout_shifts_every_cycle: assert property (
        @(posedge clk) 1'b1 |=> dout_shr == (($past(dout_shr) << 1) | $past(din_shr[DIN_N-1]))
    );

    // On stb, din_shr[0] captures the prior di value.
    check_din_lsb_captures_di: assert property (
        @(posedge clk) stb |=> din_shr[0] == $past(di)
    );

    // dout_shr[0] captures the prior MSB of din_shr every cycle.
    check_dout_lsb_captures_din_msb: assert property (
        @(posedge clk) 1'b1 |=> dout_shr[0] == $past(din_shr[DIN_N-1])
    );

    generate
        if (DIN_N > 1) begin : gen_din_shift_checks
            // On stb, upper din_shr bits shift toward the MSB.
            check_din_upper_bits_shift: assert property (
                @(posedge clk) stb |=> din_shr[DIN_N-1:1] == $past(din_shr[DIN_N-2:0])
            );
        end

        if (DOUT_N > 1) begin : gen_dout_shift_checks
            // Upper dout_shr bits shift toward the MSB every cycle.
            check_dout_upper_bits_shift: assert property (
                @(posedge clk) 1'b1 |=> dout_shr[DOUT_N-1:1] == $past(dout_shr[DOUT_N-2:0])
            );

            // The output bit advances with the dout_shr shift.
            check_do_advances_with_dout_shift: assert property (
                @(posedge clk) 1'b1 |=> do == $past(dout_shr[DOUT_N-2])
            );
        end
    endgenerate

endmodule