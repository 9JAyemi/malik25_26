module encoder43table_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y2,
    input logic Y1,
    input logic Y0
);

    // No RTL clock or reset; sample combinational behavior on the global clock.

    // The output encodes the number of asserted inputs.
    check_output_matches_input_count: assert property (
        @($global_clock)
        {Y2, Y1, Y0} == ({2'b00, A} + {2'b00, B} + {2'b00, C} + {2'b00, D})
    );

    // Zero asserted inputs encode as 000.
    check_zero_count_encoding: assert property (
        @($global_clock)
        (({2'b00, A} + {2'b00, B} + {2'b00, C} + {2'b00, D}) == 3'd0) |-> ({Y2, Y1, Y0} == 3'b000)
    );

    // One asserted input encodes as 001.
    check_one_count_encoding: assert property (
        @($global_clock)
        (({2'b00, A} + {2'b00, B} + {2'b00, C} + {2'b00, D}) == 3'd1) |-> ({Y2, Y1, Y0} == 3'b001)
    );

    // Two asserted inputs encode as 010.
    check_two_count_encoding: assert property (
        @($global_clock)
        (({2'b00, A} + {2'b00, B} + {2'b00, C} + {2'b00, D}) == 3'd2) |-> ({Y2, Y1, Y0} == 3'b010)
    );

    // Three asserted inputs encode as 011.
    check_three_count_encoding: assert property (
        @($global_clock)
        (({2'b00, A} + {2'b00, B} + {2'b00, C} + {2'b00, D}) == 3'd3) |-> ({Y2, Y1, Y0} == 3'b011)
    );

    // Four asserted inputs encode as 100.
    check_four_count_encoding: assert property (
        @($global_clock)
        (({2'b00, A} + {2'b00, B} + {2'b00, C} + {2'b00, D}) == 3'd4) |-> ({Y2, Y1, Y0} == 3'b100)
    );

    // The LSB matches the odd parity of the inputs.
    check_y0_matches_input_parity: assert property (
        @($global_clock)
        Y0 == (A ^ B ^ C ^ D)
    );

endmodule