module counter_2bit_sva (
    input  logic [1:0] Q,
    input  logic       CLK,
    input  logic       RESET_B
);

    // Reset low forces the counter output to 00.
    check_reset_forces_zero: assert property (
        @(posedge CLK) !RESET_B |-> (Q == 2'b00)
    );

    // A sampled reset keeps the counter at 00 through the next sample.
    check_reset_holds_zero_to_next_sample: assert property (
        @(posedge CLK) !RESET_B |=> (Q == 2'b00)
    );

    // From 00, the counter advances to 01 unless an async reset returns it to 00.
    check_count_00_advances_or_resets: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (Q == 2'b00) |=> ((Q == 2'b01) || (Q == 2'b00))
    );

    // From 01, the counter advances to 10 unless an async reset returns it to 00.
    check_count_01_advances_or_resets: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (Q == 2'b01) |=> ((Q == 2'b10) || (Q == 2'b00))
    );

    // From 10, the counter advances to 11 unless an async reset returns it to 00.
    check_count_10_advances_or_resets: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (Q == 2'b10) |=> ((Q == 2'b11) || (Q == 2'b00))
    );

    // From 11, the counter wraps back to 00.
    check_count_11_wraps_to_zero: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (Q == 2'b11) |=> (Q == 2'b00)
    );

endmodule