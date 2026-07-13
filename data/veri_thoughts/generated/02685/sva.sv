module xnor_xor_sva (
    input logic CLK,            // External clock for property sampling (DUT has no clock/reset)
    input logic [2:0] in1,
    input logic [2:0] in2,
    input logic [1:0] in3,
    input logic out1,
    input logic out2
);
    // out1 equals AND of XNORs of in1 and in2
    check_out1_definition: assert property (
        @(posedge CLK) out1 == (&(~(in1 ^ in2)))
    );

    // out2 equals out1 XOR in3[1]
    check_out2_definition: assert property (
        @(posedge CLK) out2 == (out1 ^ in3[1])
    );

    // If LSBs differ, out1 must be 0
    check_out1_zero_if_bit0_diff: assert property (
        @(posedge CLK) (in1[0] ^ in2[0]) |-> (out1 == 1'b0)
    );

    // If mid bits differ, out1 must be 0
    check_out1_zero_if_bit1_diff: assert property (
        @(posedge CLK) (in1[1] ^ in2[1]) |-> (out1 == 1'b0)
    );

    // If MSBs differ, out1 must be 0
    check_out1_zero_if_bit2_diff: assert property (
        @(posedge CLK) (in1[2] ^ in2[2]) |-> (out1 == 1'b0)
    );

    // If all bits match, out1 must be 1
    check_out1_one_if_all_equal: assert property (
        @(posedge CLK) (~(in1[0] ^ in2[0]) && ~(in1[1] ^ in2[1]) && ~(in1[2] ^ in2[2])) |-> (out1 == 1'b1)
    );

    // When out1 is 0, out2 equals in3[1]
    check_out2_when_out1_zero: assert property (
        @(posedge CLK) (!out1) |-> (out2 == in3[1])
    );

    // When out1 is 1, out2 equals NOT in3[1]
    check_out2_when_out1_one: assert property (
        @(posedge CLK) (out1) |-> (out2 == ~in3[1])
    );

    // Changes on in3[0] do not affect out1 if in1/in2 are stable
    check_out1_independent_of_in3_0: assert property (
        @(posedge CLK) ($changed(in3[0]) && $stable(in1) && $stable(in2)) |-> $stable(out1)
    );

    // Changes on in3[0] do not affect out2 if in1/in2/in3[1] are stable
    check_out2_independent_of_in3_0: assert property (
        @(posedge CLK) ($changed(in3[0]) && $stable(in1) && $stable(in2) && $stable(in3[1])) |-> $stable(out2)
    );

    // Toggling in3[1] toggles out2 when in1/in2 are stable
    check_out2_toggles_with_in3_1: assert property (
        @(posedge CLK) ($changed(in3[1]) && $stable(in1) && $stable(in2)) |-> $changed(out2)
    );
endmodule