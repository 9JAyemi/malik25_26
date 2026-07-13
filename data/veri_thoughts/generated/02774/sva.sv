module priority_encoder_sva (
    input logic in0,
    input logic in1,
    input logic [1:0] out
);
    // Combinational DUT with no clock/reset; sample assertions on any input edge.

    // Out must equal the encoded function of inputs.
    check_out_encoding: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1) out == {in1, (in0 && !in1)}
    );

    // If in1 is high, output must be 2'b10 (in1 has priority).
    check_in1_priority_to_10: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1) in1 |-> (out == 2'b10)
    );

    // If only in0 is high, output must be 2'b01.
    check_in0_only_to_01: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1) (in0 && !in1) |-> (out == 2'b01)
    );

    // If both inputs are low, output must be 2'b00.
    check_both_low_to_00: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1) (!in0 && !in1) |-> (out == 2'b00)
    );

    // Output must never be 2'b11.
    check_out_not_11: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1) out != 2'b11
    );

    // MSB equals in1.
    check_msb_matches_in1: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1) out[1] == in1
    );

    // LSB equals in0 & ~in1.
    check_lsb_logic: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1) out[0] == (in0 && !in1)
    );

    // If LSB is 1, then in0=1 and in1=0.
    check_lsb_one_implies_inputs: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1) out[0] |-> (in0 && !in1)
    );

    // If MSB is 1, then in1=1.
    check_msb_one_implies_in1: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1) out[1] |-> in1
    );

    // When in1 is high, LSB must be 0.
    check_lsb_zero_when_in1_high: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1) in1 |-> (out[0] == 1'b0)
    );
endmodule