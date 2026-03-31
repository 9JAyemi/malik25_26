module priority_encoder_sva #(
    parameter int n = 4,
    parameter int m = 2
) (
    input logic [n-1:0] in,
    input logic [m-1:0] out
);

    // out must match the RTL casez priority encoding.
    check_out_matches_casez_encoding: assert property (
        @($global_clock)
        out == (in[3] ? 2'b00 :
                in[2] ? 2'b01 :
                in[1] ? 2'b10 :
                in[0] ? 2'b11 :
                         2'b00)
    );

    // in[3] has highest priority and encodes to 00.
    check_in3_priority: assert property (
        @($global_clock)
        in[3] |-> (out == 2'b00)
    );

    // in[2] is selected when in[3] is low and encodes to 01.
    check_in2_priority: assert property (
        @($global_clock)
        (!in[3] && in[2]) |-> (out == 2'b01)
    );

    // in[1] is selected when in[3:2] are low and encodes to 10.
    check_in1_priority: assert property (
        @($global_clock)
        (!in[3] && !in[2] && in[1]) |-> (out == 2'b10)
    );

    // in[0] is selected when in[3:1] are low and encodes to 11.
    check_in0_priority: assert property (
        @($global_clock)
        (!in[3] && !in[2] && !in[1] && in[0]) |-> (out == 2'b11)
    );

    // No asserted input encodes to 00.
    check_default_zero_when_no_input: assert property (
        @($global_clock)
        (!in[3] && !in[2] && !in[1] && !in[0]) |-> (out == 2'b00)
    );

    // out can only be 00 when in[3] is high or no input is asserted.
    check_out_zero_only_when_in3_or_no_input: assert property (
        @($global_clock)
        (out == 2'b00) |-> (in[3] || (!in[3] && !in[2] && !in[1] && !in[0]))
    );

    // out can only be 01 when in[2] is high and in[3] is low.
    check_out_one_only_when_in2_and_not_in3: assert property (
        @($global_clock)
        (out == 2'b01) |-> (!in[3] && in[2])
    );

    // out can only be 10 when in[1] is high and in[3:2] are low.
    check_out_two_only_when_in1_and_not_in32: assert property (
        @($global_clock)
        (out == 2'b10) |-> (!in[3] && !in[2] && in[1])
    );

    // out can only be 11 when in[0] is high and in[3:1] are low.
    check_out_three_only_when_in0_and_not_in31: assert property (
        @($global_clock)
        (out == 2'b11) |-> (!in[3] && !in[2] && !in[1] && in[0])
    );

endmodule