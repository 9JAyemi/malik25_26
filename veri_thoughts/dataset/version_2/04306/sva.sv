module four_to_one_assertions (
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic out
);

    // out must equal the OR of all pairwise input AND terms.
    check_out_matches_pairwise_or: assert property (
        @($global_clock)
        out == ((in1 && in2) || (in1 && in3) || (in1 && in4) ||
                (in2 && in3) || (in2 && in4) || (in3 && in4))
    );

    // Any time at least one input pair is high, out must be high.
    check_at_least_one_pair_high_sets_out: assert property (
        @($global_clock)
        (((in1 && in2) || (in1 && in3) || (in1 && in4) ||
          (in2 && in3) || (in2 && in4) || (in3 && in4)) |-> out)
    );

    // If no input pair is high, out must be low.
    check_no_pair_high_clears_out: assert property (
        @($global_clock)
        ((!((in1 && in2) || (in1 && in3) || (in1 && in4) ||
            (in2 && in3) || (in2 && in4) || (in3 && in4))) |-> !out)
    );

    // All inputs low must produce a low output.
    check_all_zero_inputs_clear_out: assert property (
        @($global_clock)
        ((!in1 && !in2 && !in3 && !in4) |-> !out)
    );

    // Any one-hot input pattern must produce a low output.
    check_one_hot_inputs_clear_out: assert property (
        @($global_clock)
        ((( in1 && !in2 && !in3 && !in4) ||
          (!in1 &&  in2 && !in3 && !in4) ||
          (!in1 && !in2 &&  in3 && !in4) ||
          (!in1 && !in2 && !in3 &&  in4)) |-> !out)
    );

    // Any exactly-two-hot input pattern must produce a high output.
    check_exactly_two_high_sets_out: assert property (
        @($global_clock)
        ((( in1 &&  in2 && !in3 && !in4) ||
          ( in1 && !in2 &&  in3 && !in4) ||
          ( in1 && !in2 && !in3 &&  in4) ||
          (!in1 &&  in2 &&  in3 && !in4) ||
          (!in1 &&  in2 && !in3 &&  in4) ||
          (!in1 && !in2 &&  in3 &&  in4)) |-> out)
    );

    // Any exactly-three-hot input pattern must produce a high output.
    check_exactly_three_high_sets_out: assert property (
        @($global_clock)
        (((!in1 &&  in2 &&  in3 &&  in4) ||
          ( in1 && !in2 &&  in3 &&  in4) ||
          ( in1 &&  in2 && !in3 &&  in4) ||
          ( in1 &&  in2 &&  in3 && !in4)) |-> out)
    );

    // All inputs high must produce a high output.
    check_all_one_inputs_set_out: assert property (
        @($global_clock)
        ((in1 && in2 && in3 && in4) |-> out)
    );

    // A high output must be justified by at least one high input pair.
    check_out_high_implies_some_pair_high: assert property (
        @($global_clock)
        (out |-> ((in1 && in2) || (in1 && in3) || (in1 && in4) ||
                  (in2 && in3) || (in2 && in4) || (in3 && in4)))
    );

    // A low output means no input pair is simultaneously high.
    check_out_low_implies_no_pair_high: assert property (
        @($global_clock)
        ((!out) |-> !((in1 && in2) || (in1 && in3) || (in1 && in4) ||
                       (in2 && in3) || (in2 && in4) || (in3 && in4)))
    );

endmodule