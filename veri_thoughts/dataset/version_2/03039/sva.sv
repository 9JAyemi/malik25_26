module sequence_detector_sva #(parameter int n = 4) (
    input logic inp,
    input logic out,
    input logic [n-1:0] shift_reg
);

    localparam logic [n-1:0] state_1 = 4'b0011;
    localparam logic [n-1:0] state_2 = 4'b0110;
    localparam logic [n-1:0] state_3 = 4'b1100;
    localparam logic [n-1:0] state_4 = 4'b1001;

    // The sampled shift register is the previous sampled value shifted in with a 1.
    check_shift_reg_update: assert property (
        @(posedge inp)
        ($past(1'b1) === 1'b1) |-> (shift_reg == {$past(shift_reg[n-2:0]), 1'b1})
    );

    // After one prior inp edge, the LSB of the register is set.
    check_shift_reg_lsb_one: assert property (
        @(posedge inp)
        ($past(1'b1) === 1'b1) |-> (shift_reg[0] == 1'b1)
    );

    // After two prior inp edges, the two LSBs of the register are set.
    check_shift_reg_two_lsbs_one: assert property (
        @(posedge inp)
        ($past(1'b1, 2) === 1'b1) |-> (shift_reg[1:0] == 2'b11)
    );

    // After three prior inp edges, the three LSBs of the register are set.
    check_shift_reg_three_lsbs_one: assert property (
        @(posedge inp)
        ($past(1'b1, 3) === 1'b1) |-> (shift_reg[2:0] == 3'b111)
    );

    // After four prior inp edges, the register is all ones.
    check_shift_reg_all_ones: assert property (
        @(posedge inp)
        ($past(1'b1, 4) === 1'b1) |-> (shift_reg == 4'b1111)
    );

    // A matching prior shift register state drives out high on the next sampled edge.
    check_out_high_on_matching_prior_state: assert property (
        @(posedge inp)
        (($past(1'b1) === 1'b1) &&
         (($past(shift_reg) == state_1) ||
          ($past(shift_reg) == state_2) ||
          ($past(shift_reg) == state_3) ||
          ($past(shift_reg) == state_4))) |-> (out == 1'b1)
    );

    // A non-matching prior shift register state drives out low on the next sampled edge.
    check_out_low_on_nonmatching_prior_state: assert property (
        @(posedge inp)
        (($past(1'b1) === 1'b1) &&
         !(($past(shift_reg) == state_1) ||
           ($past(shift_reg) == state_2) ||
           ($past(shift_reg) == state_3) ||
           ($past(shift_reg) == state_4))) |-> (out == 1'b0)
    );

    // After three prior inp edges, the current register value cannot match any listed state.
    check_no_state_match_after_three_edges: assert property (
        @(posedge inp)
        ($past(1'b1, 3) === 1'b1) |-> !((shift_reg == state_1) ||
                                        (shift_reg == state_2) ||
                                        (shift_reg == state_3) ||
                                        (shift_reg == state_4))
    );

    // After four prior inp edges, the output must be low.
    check_out_low_after_four_edges: assert property (
        @(posedge inp)
        ($past(1'b1, 4) === 1'b1) |-> (out == 1'b0)
    );

endmodule