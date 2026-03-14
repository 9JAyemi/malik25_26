module CRC_16_sva (
    input  logic        BITVAL,
    input  logic        Enable,
    input  logic        CLK,
    input  logic        RST,
    input  logic [15:0] CRC
);
    ///// Reset behavior /////
    // While reset is asserted at the clock edge, CRC must be zero.
    reset_forces_zero: assert property (
        @(posedge CLK) RST |-> (CRC == 16'h0000)
    );

    ///// CRC update on Enable /////
    // On enable, CRC[15] takes previous CRC[14].
    update_shift_15: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[15] == $past(CRC[14]))
    );
    // On enable, CRC[14] takes previous CRC[13].
    update_shift_14: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[14] == $past(CRC[13]))
    );
    // On enable, CRC[13] takes previous CRC[12].
    update_shift_13: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[13] == $past(CRC[12]))
    );
    // On enable, CRC[12] gets prev CRC[11] XOR prev(BITVAL ^ CRC[15]).
    update_xor_12: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[12] == ($past(CRC[11]) ^ ($past(BITVAL) ^ $past(CRC[15]))))
    );
    // On enable, CRC[11] takes previous CRC[10].
    update_shift_11: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[11] == $past(CRC[10]))
    );
    // On enable, CRC[10] takes previous CRC[9].
    update_shift_10: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[10] == $past(CRC[9]))
    );
    // On enable, CRC[9] takes previous CRC[8].
    update_shift_9: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[9] == $past(CRC[8]))
    );
    // On enable, CRC[8] takes previous CRC[7].
    update_shift_8: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[8] == $past(CRC[7]))
    );
    // On enable, CRC[7] takes previous CRC[6].
    update_shift_7: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[7] == $past(CRC[6]))
    );
    // On enable, CRC[6] takes previous CRC[5].
    update_shift_6: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[6] == $past(CRC[5]))
    );
    // On enable, CRC[5] gets prev CRC[4] XOR prev(BITVAL ^ CRC[15]).
    update_xor_5: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[5] == ($past(CRC[4]) ^ ($past(BITVAL) ^ $past(CRC[15]))))
    );
    // On enable, CRC[4] takes previous CRC[3].
    update_shift_4: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[4] == $past(CRC[3]))
    );
    // On enable, CRC[3] takes previous CRC[2].
    update_shift_3: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[3] == $past(CRC[2]))
    );
    // On enable, CRC[2] takes previous CRC[1].
    update_shift_2: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[2] == $past(CRC[1]))
    );
    // On enable, CRC[1] takes previous CRC[0].
    update_shift_1: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[1] == $past(CRC[0]))
    );
    // On enable, CRC[0] gets prev(BITVAL ^ CRC[15]).
    update_xor_0: assert property (
        @(posedge CLK) disable iff (RST) (Enable && !$past(RST)) |-> (CRC[0] == ($past(BITVAL) ^ $past(CRC[15])))
    );
endmodule