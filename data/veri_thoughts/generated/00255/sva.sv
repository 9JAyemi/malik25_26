module comparator_sva (
    input logic       clk,
    input logic [1:0] in_0,
    input logic [1:0] in_1,
    input logic [1:0] out
);

    // Greater-than inputs encode as 01.
    check_gt_encoding: assert property (
        @(posedge clk)
        (!$isunknown({in_0, in_1}) && (in_0 > in_1)) |-> (out === 2'b01)
    );

    // Equal inputs encode as 10.
    check_eq_encoding: assert property (
        @(posedge clk)
        (!$isunknown({in_0, in_1}) && (in_0 == in_1)) |-> (out === 2'b10)
    );

    // Less-than inputs encode as 00.
    check_lt_encoding: assert property (
        @(posedge clk)
        (!$isunknown({in_0, in_1}) && (in_0 < in_1)) |-> (out === 2'b00)
    );

    // Output is always one of the implemented encodings.
    check_valid_output_code: assert property (
        @(posedge clk)
        (out === 2'b00) || (out === 2'b01) || (out === 2'b10)
    );

    // out[0] is asserted only for the greater-than case.
    check_bit0_tracks_gt: assert property (
        @(posedge clk)
        (!$isunknown({in_0, in_1})) |-> (out[0] === (in_0 > in_1))
    );

    // out[1] is asserted only for the equal case.
    check_bit1_tracks_eq: assert property (
        @(posedge clk)
        (!$isunknown({in_0, in_1})) |-> (out[1] === (in_0 == in_1))
    );

    // Stable inputs keep the combinational output stable.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk)
        $stable({in_0, in_1}) |-> $stable(out)
    );

endmodule