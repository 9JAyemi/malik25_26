module ram_RAMB18E1_sva #(
    parameter string WRITE_MODE_A = "WRITE_FIRST"
) (
    input  logic        clk,
    input  logic [7:0]  din,
    input  logic [7:0]  dout
);

    // WRITE_FIRST behavior: dout updates to {prev din[0], prev dout[7:1]} each cycle.
    generate if (WRITE_MODE_A == "WRITE_FIRST") begin : gen_writefirst
        check_writefirst_dout_update: assert property (
            @(posedge clk) 1'b1 |-> (dout == { $past(din[0]), $past(dout[7:1]) })
        );
        // WRITE_FIRST: MSB of dout comes from previous din[0].
        check_writefirst_msb_from_din0: assert property (
            @(posedge clk) 1'b1 |-> (dout[7] == $past(din[0]))
        );
        // WRITE_FIRST: lower 7 bits shift right from previous dout.
        check_writefirst_lower_bits_shift: assert property (
            @(posedge clk) 1'b1 |-> (dout[6:0] == $past(dout[7:1]))
        );
        // WRITE_FIRST: LSB equals previous dout[1].
        check_writefirst_lsb_from_prev_bit1: assert property (
            @(posedge clk) 1'b1 |-> (dout[0] == $past(dout[1]))
        );
    end else begin : gen_not_writefirst
        // Non-WRITE_FIRST: dout holds its value across cycles.
        check_nowrite_hold: assert property (
            @(posedge clk) 1'b1 |-> (dout == $past(dout))
        );
        // Non-WRITE_FIRST: MSB holds.
        check_nowrite_msb_hold: assert property (
            @(posedge clk) 1'b1 |-> (dout[7] == $past(dout[7]))
        );
        // Non-WRITE_FIRST: lower bits hold.
        check_nowrite_lower_bits_hold: assert property (
            @(posedge clk) 1'b1 |-> (dout[6:0] == $past(dout[6:0]))
        );
    end endgenerate

endmodule