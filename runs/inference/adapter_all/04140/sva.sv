module odd_even_sva (
    input logic [2:0] input_bits,
    input logic [1:0] output_bits
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // Output must always be either 01 or 10.
    check_output_legal_values: assert property (
        @($global_clock) (output_bits == 2'b01) || (output_bits == 2'b10)
    );

    // LSB 0 selects 10.
    check_lsb_zero_selects_10: assert property (
        @($global_clock) (input_bits[0] == 1'b0) |-> (output_bits == 2'b10)
    );

    // LSB 1 selects 01.
    check_lsb_one_selects_01: assert property (
        @($global_clock) (input_bits[0] == 1'b1) |-> (output_bits == 2'b01)
    );

    // Output 01 implies LSB is 1.
    check_output_01_implies_lsb_one: assert property (
        @($global_clock) (output_bits == 2'b01) |-> (input_bits[0] == 1'b1)
    );

    // Output 10 implies LSB is 0.
    check_output_10_implies_lsb_zero: assert property (
        @($global_clock) (output_bits == 2'b10) |-> (input_bits[0] == 1'b0)
    );

    // Output bits are the inverse of each other.
    check_output_bits_inverse: assert property (
        @($global_clock) (output_bits[1] == ~output_bits[0])
    );

endmodule