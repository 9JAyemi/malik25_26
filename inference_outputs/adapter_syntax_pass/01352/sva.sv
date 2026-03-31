module binary_to_gray_sva (
    input logic [3:0] in,
    input logic       load,
    input logic [3:0] out,
    input logic       valid
);

    // valid is asserted on the cycle after load is asserted.
    check_valid_asserts_on_load: assert property (
        @(posedge load) 1'b1 |=> (valid == 1'b1)
    );

    // valid is deasserted on the cycle after load is deasserted.
    check_valid_deasserts_on_no_load: assert property (
        @(negedge load) 1'b1 |=> (valid == 1'b0)
    );

    // out is the previous cycle's registered Gray-code value.
    check_out_matches_previous_gray: assert property (
        @(posedge load) 1'b1 |=> (out == $past((in >> 1) ^ in))
    );

    // valid is high exactly one cycle after load is asserted.
    check_valid_one_cycle_after_load: assert property (
        @(posedge load) 1'b1 |=> (valid == 1'b1) ##1 (valid == 1'b0)
    );

    // valid is low exactly one cycle after load is deasserted.
    check_valid_one_cycle_after_no_load: assert property (
        @(negedge load) 1'b1 |=> (valid == 1'b0) ##1 (valid == 1'b1)
    );

endmodule