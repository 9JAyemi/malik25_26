module CRC5_D5_solution_sva (
    input logic [4:0] nextCRC5_D5,
    input logic [4:0] Data,
    input logic [4:0] crc
);
    // Expected combinational mapping per RTL
    logic [4:0] exp;
    assign exp[0] = Data[3] ^ Data[0] ^ crc[0] ^ crc[3];
    assign exp[1] = Data[4] ^ Data[1] ^ crc[1] ^ crc[4];
    assign exp[2] = Data[3] ^ Data[2] ^ Data[0] ^ crc[0] ^ crc[2] ^ crc[3];
    assign exp[3] = Data[4] ^ Data[3] ^ Data[1] ^ crc[1] ^ crc[3] ^ crc[4];
    assign exp[4] = Data[4] ^ Data[2] ^ crc[2] ^ crc[4];

    // Output equals the defined XOR function of inputs at all times.
    check_crc_function_vector: assert property (
        @($global_clock) nextCRC5_D5 == exp
    );

    // Output holds value when inputs hold value (no spurious changes).
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock) (Data == $past(Data) && crc == $past(crc)) |-> (nextCRC5_D5 == $past(nextCRC5_D5))
    );

    // Bit0 unaffected if its dependent inputs are unchanged.
    check_bit0_independence: assert property (
        @($global_clock)
        (Data[3] == $past(Data[3]) && Data[0] == $past(Data[0]) && crc[0] == $past(crc[0]) && crc[3] == $past(crc[3]))
        |-> (nextCRC5_D5[0] == $past(nextCRC5_D5[0]))
    );

    // Bit2 unaffected if its dependent inputs are unchanged.
    check_bit2_independence: assert property (
        @($global_clock)
        (Data[3] == $past(Data[3]) && Data[2] == $past(Data[2]) && Data[0] == $past(Data[0]) &&
         crc[0] == $past(crc[0]) && crc[2] == $past(crc[2]) && crc[3] == $past(crc[3]))
        |-> (nextCRC5_D5[2] == $past(nextCRC5_D5[2]))
    );

    // Bit4 unaffected if its dependent inputs are unchanged.
    check_bit4_independence: assert property (
        @($global_clock)
        (Data[4] == $past(Data[4]) && Data[2] == $past(Data[2]) && crc[2] == $past(crc[2]) && crc[4] == $past(crc[4]))
        |-> (nextCRC5_D5[4] == $past(nextCRC5_D5[4]))
    );

    // If only Data[0] toggles among Bit2 dependencies, Bit2 toggles.
    check_bit2_toggle_from_Data0: assert property (
        @($global_clock)
        $changed(Data[0]) &&
        !$changed(Data[3]) && !$changed(Data[2]) &&
        !$changed(crc[0]) && !$changed(crc[2]) && !$changed(crc[3])
        |-> $changed(nextCRC5_D5[2])
    );

    // If only crc[4] toggles among Bit3 dependencies, Bit3 toggles.
    check_bit3_toggle_from_crc4: assert property (
        @($global_clock)
        $changed(crc[4]) &&
        !$changed(Data[4]) && !$changed(Data[3]) && !$changed(Data[1]) &&
        !$changed(crc[1]) && !$changed(crc[3])
        |-> $changed(nextCRC5_D5[3])
    );
endmodule