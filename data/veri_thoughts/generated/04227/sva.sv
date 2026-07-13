module SIPO_sva (
    input logic       clk,
    input logic       rst,
    input logic       SerialIn,
    input logic [3:0] BusOut
);

    // A sampled reset cycle clears the parallel output by the next clock.
    check_reset_clears_busout: assert property (
        @(posedge clk) !rst |=> (BusOut == 4'b0000)
    );

    // The sampled output remains zero on the first cycle after reset release.
    check_reset_release_keeps_zero_before_shift: assert property (
        @(posedge clk) (!rst ##1 rst) |-> (BusOut == 4'b0000)
    );

    // In normal operation, the output shifts left and loads SerialIn into bit 0.
    check_shift_register_update: assert property (
        @(posedge clk) disable iff (!rst)
        1'b1 |=> (BusOut == { $past(BusOut[2:0]), $past(SerialIn) })
    );

    // Bit 3 takes the previous value of bit 2.
    check_bit3_shift_from_bit2: assert property (
        @(posedge clk) disable iff (!rst)
        1'b1 |=> (BusOut[3] == $past(BusOut[2]))
    );

    // Bit 2 takes the previous value of bit 1.
    check_bit2_shift_from_bit1: assert property (
        @(posedge clk) disable iff (!rst)
        1'b1 |=> (BusOut[2] == $past(BusOut[1]))
    );

    // Bit 1 takes the previous value of bit 0.
    check_bit1_shift_from_bit0: assert property (
        @(posedge clk) disable iff (!rst)
        1'b1 |=> (BusOut[1] == $past(BusOut[0]))
    );

    // Bit 0 captures the previous SerialIn value.
    check_bit0_captures_serialin: assert property (
        @(posedge clk) disable iff (!rst)
        1'b1 |=> (BusOut[0] == $past(SerialIn))
    );

endmodule