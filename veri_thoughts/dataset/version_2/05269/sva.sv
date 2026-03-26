module barrel_shifter_sva (
    input logic [3:0] DATA,
    input logic [1:0] SHIFT,
    input logic [3:0] OUT
);

    // OUT[3] matches the implemented combinational expression.
    check_out3_function: assert property (
        @($global_clock)
        OUT[3] == (SHIFT[1] ? DATA[1] :
                  (SHIFT[0] ? DATA[2] :
                  (SHIFT[0] ? DATA[2] :
                  (SHIFT[1] ? DATA[2] :
                  (SHIFT[1] ? DATA[0] : 1'b0)))))
    );

    // OUT[2] matches the implemented combinational expression.
    check_out2_function: assert property (
        @($global_clock)
        OUT[2] == (SHIFT[1] ? DATA[0] :
                  (SHIFT[0] ? DATA[3] :
                  (SHIFT[0] ? DATA[3] :
                  (SHIFT[1] ? DATA[1] :
                  (SHIFT[1] ? DATA[3] : 1'b0)))))
    );

    // OUT[1] matches the implemented combinational expression.
    check_out1_function: assert property (
        @($global_clock)
        OUT[1] == (SHIFT[1] ? DATA[3] :
                  (SHIFT[0] ? DATA[2] :
                  (SHIFT[0] ? DATA[2] :
                  (SHIFT[1] ? DATA[0] :
                  (SHIFT[1] ? DATA[1] : 1'b0)))))
    );

    // OUT[0] matches the implemented combinational expression.
    check_out0_function: assert property (
        @($global_clock)
        OUT[0] == (SHIFT[1] ? DATA[2] :
                  (SHIFT[0] ? DATA[1] :
                  (SHIFT[0] ? DATA[1] :
                  (SHIFT[1] ? DATA[3] :
                  (SHIFT[1] ? DATA[2] : 1'b0)))))
    );

    // SHIFT=00 drives all outputs low.
    check_shift00_zero_output: assert property (
        @($global_clock)
        (SHIFT == 2'b00) |-> (OUT == 4'b0000)
    );

    // SHIFT=01 produces the implemented output mapping.
    check_shift01_output_map: assert property (
        @($global_clock)
        (SHIFT == 2'b01) |-> (OUT == {DATA[2], DATA[3], DATA[2], DATA[1]})
    );

    // SHIFT[1] has priority and selects the implemented output mapping.
    check_shift1_priority_output_map: assert property (
        @($global_clock)
        (SHIFT[1] == 1'b1) |-> (OUT == {DATA[1], DATA[0], DATA[3], DATA[2]})
    );

endmodule