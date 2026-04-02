module power_good_sva (
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic in5,
    input logic in6,
    input logic in7,
    input logic in8,
    input logic in9,
    output logic out1
);
    // Combinational logic, so use @(posedge clk) for assertions

    // out1 is the output of a series of AND gates and a buffer
    // Ensure that out1 is only HIGH when the final AND gate (and7_out) is HIGH
    output_check: assert property (
        @(posedge clk) disable iff (!reset_n) out1 |-> and7_out
    ) else $error("out1 is HIGH when and7_out is LOW");

    // Ensure that and7_out is the result of the final AND gate
    and7_out_check: assert property (
        @(posedge clk) disable iff (!reset_n) and7_out |-> (and6_out && in9)
    ) else $error("and7_out is not the result of and6_out and in9");

    // Ensure that and6_out is the result of the AND gate combining and4_out and and5_out
    and6_out_check: assert property (
        @(posedge clk) disable iff (!reset_n) and6_out |-> (and4_out && and5_out)
    ) else $error("and6_out is not the result of and4_out and and5_out");

    // Ensure that and5_out is the result of the AND gate combining and2_out and and3_out
    and5_out_check: assert property (
        @(posedge clk) disable iff (!reset_n) and5_out |-> (and2_out && and3_out)
    ) else $error("and5_out is not the result of and2_out and and3_out");

    // Ensure that and4_out is the result of the AND gate combining and0_out and and1_out
    and4_out_check: assert property (
        @(posedge clk) disable iff (!reset_n) and4_out |-> (and0_out && and1_out)
    ) else $error("and4_out is not the result of and0_out and and1_out");

    // Ensure that and3_out is the result of the AND gate combining in7 and in8
    and3_out_check: assert property (
        @(posedge clk) disable iff (!reset_n) and3_out |-> (in7 && in8)
    ) else $error("and3_out is not the result of in7 and in8");

    // Ensure that and2_out is the result of the AND gate combining in5 and in6
    and2_out_check: assert property (
        @(posedge clk) disable iff (!reset_n) and2_out |-> (in5 && in6)
    ) else $error("and2_out is not the result of in5 and in6");

    // Ensure that and1_out is the result of the AND gate combining in3 and in4
    and1_out_check: assert property (
        @(posedge clk) disable iff (!reset_n) and1_out |-> (in3 && in4)
    ) else $error("and1_out is not the result of in3 and in4");

    // Ensure that and0_out is the result of the AND gate combining in1 and in2
    and0_out_check: assert property (
        @(posedge clk) disable iff (!reset_n) and0_out |-> (in1 && in2)
    ) else $error("and0_out is not the result of in1 and in2");

    // Ensure that out1 is LOW when reset_n is LOW
    reset_check: assert property (
        @(posedge clk) !reset_n |-> out1 == 1'b0
    ) else $error("out1 is HIGH when reset_n is LOW");
endmodule