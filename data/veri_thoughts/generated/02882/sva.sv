module verilog_module_sva (
    input logic CLK,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic in5,
    input logic in6,
    input logic in7,
    input logic in8,
    input logic out1,
    input logic out2,
    input logic out3,
    input logic out4
);
    ///// out1 = in1 & in2 & in3 /////
    // out1 equals bitwise AND of in1,in2,in3.
    check_out1_is_and: assert property (
        @(posedge CLK) out1 === (in1 & in2 & in3)
    );
    // If out1 is 1 then all in1,in2,in3 are 1.
    check_out1_high_inputs_all_high: assert property (
        @(posedge CLK) (out1 == 1'b1) |-> ((in1 == 1'b1) && (in2 == 1'b1) && (in3 == 1'b1))
    );
    // If in1 is 0 then out1 is 0.
    check_in1_zero_forces_out1_zero: assert property (
        @(posedge CLK) (in1 == 1'b0) |-> (out1 == 1'b0)
    );
    // If in2 is 0 then out1 is 0.
    check_in2_zero_forces_out1_zero: assert property (
        @(posedge CLK) (in2 == 1'b0) |-> (out1 == 1'b0)
    );
    // If in3 is 0 then out1 is 0.
    check_in3_zero_forces_out1_zero: assert property (
        @(posedge CLK) (in3 == 1'b0) |-> (out1 == 1'b0)
    );

    ///// out2 = in4 | in5 | in6 /////
    // out2 equals bitwise OR of in4,in5,in6.
    check_out2_is_or: assert property (
        @(posedge CLK) out2 === (in4 | in5 | in6)
    );
    // If out2 is 0 then all in4,in5,in6 are 0.
    check_out2_low_inputs_all_low: assert property (
        @(posedge CLK) (out2 == 1'b0) |-> ((in4 == 1'b0) && (in5 == 1'b0) && (in6 == 1'b0))
    );
    // If in4 is 1 then out2 is 1.
    check_in4_one_forces_out2_one: assert property (
        @(posedge CLK) (in4 == 1'b1) |-> (out2 == 1'b1)
    );
    // If in5 is 1 then out2 is 1.
    check_in5_one_forces_out2_one: assert property (
        @(posedge CLK) (in5 == 1'b1) |-> (out2 == 1'b1)
    );
    // If in6 is 1 then out2 is 1.
    check_in6_one_forces_out2_one: assert property (
        @(posedge CLK) (in6 == 1'b1) |-> (out2 == 1'b1)
    );

    ///// out3 = in7 ^ in8 /////
    // out3 equals bitwise XOR of in7,in8.
    check_out3_is_xor: assert property (
        @(posedge CLK) out3 === (in7 ^ in8)
    );
    // If in7=0 and in8=0 then out3=0.
    check_xor_00_is_0: assert property (
        @(posedge CLK) ((in7 == 1'b0) && (in8 == 1'b0)) |-> (out3 == 1'b0)
    );
    // If in7=1 and in8=1 then out3=0.
    check_xor_11_is_0: assert property (
        @(posedge CLK) ((in7 == 1'b1) && (in8 == 1'b1)) |-> (out3 == 1'b0)
    );
    // If in7=1 and in8=0 then out3=1.
    check_xor_10_is_1: assert property (
        @(posedge CLK) ((in7 == 1'b1) && (in8 == 1'b0)) |-> (out3 == 1'b1)
    );
    // If in7=0 and in8=1 then out3=1.
    check_xor_01_is_1: assert property (
        @(posedge CLK) ((in7 == 1'b0) && (in8 == 1'b1)) |-> (out3 == 1'b1)
    );

    ///// out4 = ~in1 /////
    // out4 equals bitwise NOT of in1.
    check_out4_is_not: assert property (
        @(posedge CLK) out4 === (~in1)
    );
    // If in1 is 1 then out4 is 0.
    check_not_in1_1_out4_0: assert property (
        @(posedge CLK) (in1 == 1'b1) |-> (out4 == 1'b0)
    );
    // If in1 is 0 then out4 is 1.
    check_not_in1_0_out4_1: assert property (
        @(posedge CLK) (in1 == 1'b0) |-> (out4 == 1'b1)
    );
endmodule