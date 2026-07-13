module majority_parity_xor_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic out
);

    // Output matches the RTL majority XOR parity equation.
    check_out_matches_rtl_definition: assert property (
        @(posedge clk)
        out == (
            ((in1 & in2 & in3) |
             (in1 & in2 & in4) |
             (in1 & in3 & in4) |
             (in2 & in3 & in4)) ^
            (in1 ^ in2 ^ in3 ^ in4)
        )
    );

    // All inputs low must drive the output low.
    check_all_zero_output_low: assert property (
        @(posedge clk)
        (!in1 && !in2 && !in3 && !in4) |-> (out == 1'b0)
    );

    // A one-hot input pattern must drive the output high.
    check_one_hot_output_high: assert property (
        @(posedge clk)
        (
            ( in1 && !in2 && !in3 && !in4) ||
            (!in1 &&  in2 && !in3 && !in4) ||
            (!in1 && !in2 &&  in3 && !in4) ||
            (!in1 && !in2 && !in3 &&  in4)
        ) |-> (out == 1'b1)
    );

    // Any two-high input pattern must drive the output low.
    check_two_high_output_low: assert property (
        @(posedge clk)
        (
            ( in1 &&  in2 && !in3 && !in4) ||
            ( in1 && !in2 &&  in3 && !in4) ||
            ( in1 && !in2 && !in3 &&  in4) ||
            (!in1 &&  in2 &&  in3 && !in4) ||
            (!in1 &&  in2 && !in3 &&  in4) ||
            (!in1 && !in2 &&  in3 &&  in4)
        ) |-> (out == 1'b0)
    );

    // Any three-high input pattern must drive the output low.
    check_three_high_output_low: assert property (
        @(posedge clk)
        (
            (!in1 &&  in2 &&  in3 &&  in4) ||
            ( in1 && !in2 &&  in3 &&  in4) ||
            ( in1 &&  in2 && !in3 &&  in4) ||
            ( in1 &&  in2 &&  in3 && !in4)
        ) |-> (out == 1'b0)
    );

    // All inputs high must drive the output high.
    check_all_one_output_high: assert property (
        @(posedge clk)
        (in1 && in2 && in3 && in4) |-> (out == 1'b1)
    );

endmodule