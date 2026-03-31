module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic [1:0] shift_amount,
    input logic [3:0] data_out
);

    ///// Bit-level mapping matches RTL assigns /////
    // data_out[0] selects data_in[shift_amount] per RTL
    check_bit0_mapping: assert property (
        @(posedge clk) data_out[0] == ((shift_amount == 2'b00) ? data_in[0] :
                                       (shift_amount == 2'b01) ? data_in[1] :
                                       (shift_amount == 2'b10) ? data_in[2] :
                                                                 data_in[3])
    );
    // data_out[1] selects data_in[(shift_amount+1) mod 4] per RTL
    check_bit1_mapping: assert property (
        @(posedge clk) data_out[1] == ((shift_amount == 2'b00) ? data_in[1] :
                                       (shift_amount == 2'b01) ? data_in[2] :
                                       (shift_amount == 2'b10) ? data_in[3] :
                                                                 data_in[0])
    );
    // data_out[2] selects data_in[(shift_amount+2) mod 4] per RTL
    check_bit2_mapping: assert property (
        @(posedge clk) data_out[2] == ((shift_amount == 2'b00) ? data_in[2] :
                                       (shift_amount == 2'b01) ? data_in[3] :
                                       (shift_amount == 2'b10) ? data_in[0] :
                                                                 data_in[1])
    );
    // data_out[3] selects data_in[(shift_amount+3) mod 4] per RTL
    check_bit3_mapping: assert property (
        @(posedge clk) data_out[3] == ((shift_amount == 2'b00) ? data_in[3] :
                                       (shift_amount == 2'b01) ? data_in[0] :
                                       (shift_amount == 2'b10) ? data_in[1] :
                                                                 data_in[2])
    );

    ///// Vector-level equivalence for each shift value /////
    // No shift when shift_amount == 2'b00
    check_shift0_identity: assert property (
        @(posedge clk) (shift_amount == 2'b00) |-> (data_out == data_in)
    );
    // Mapping when shift_amount == 2'b01
    check_shift1_mapping: assert property (
        @(posedge clk) (shift_amount == 2'b01) |-> (data_out == {data_in[0], data_in[1], data_in[2], data_in[3]})
    );
    // Mapping when shift_amount == 2'b10
    check_shift2_mapping: assert property (
        @(posedge clk) (shift_amount == 2'b10) |-> (data_out == {data_in[1], data_in[0], data_in[3], data_in[2]})
    );
    // Mapping when shift_amount == 2'b11
    check_shift3_mapping: assert property (
        @(posedge clk) (shift_amount == 2'b11) |-> (data_out == {data_in[2], data_in[1], data_in[0], data_in[3]})
    );

    ///// Invariants implied by permutation /////
    // Parity is preserved by rotation
    check_parity_preserved: assert property (
        @(posedge clk) (^data_out) == (^data_in)
    );
    // Number of 1s is preserved by rotation
    check_ones_count_preserved: assert property (
        @(posedge clk) $countones(data_out) == $countones(data_in)
    );

endmodule