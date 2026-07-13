module power_good_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic in5,
    input logic in6,
    input logic in7,
    input logic in8,
    input logic in9,
    input logic out1,
    input logic and0_out,
    input logic and1_out,
    input logic and2_out,
    input logic and3_out,
    input logic and4_out,
    input logic and5_out,
    input logic and6_out,
    input logic and7_out
);
    // Combinational module; no reset in RTL. clk is a sampling clock for SVA.
    // out1 is the AND of in1..in9 via the internal and*_out chain.

    // and0 implements in1 & in2.
    check_and0_func: assert property (
        @(posedge clk) and0_out == (in1 & in2)
    );

    // and1 implements in3 & in4.
    check_and1_func: assert property (
        @(posedge clk) and1_out == (in3 & in4)
    );

    // and2 implements in5 & in6.
    check_and2_func: assert property (
        @(posedge clk) and2_out == (in5 & in6)
    );

    // and3 implements in7 & in8.
    check_and3_func: assert property (
        @(posedge clk) and3_out == (in7 & in8)
    );

    // and4 combines and0_out & and1_out.
    check_and4_func: assert property (
        @(posedge clk) and4_out == (and0_out & and1_out)
    );

    // and5 combines and2_out & and3_out.
    check_and5_func: assert property (
        @(posedge clk) and5_out == (and2_out & and3_out)
    );

    // and6 combines and4_out & and5_out.
    check_and6_func: assert property (
        @(posedge clk) and6_out == (and4_out & and5_out)
    );

    // and7 combines and6_out & in9.
    check_and7_func: assert property (
        @(posedge clk) and7_out == (and6_out & in9)
    );

    // buf drives out1 from and7_out.
    check_buf_func: assert property (
        @(posedge clk) out1 == and7_out
    );

    // out1 equals the AND of all nine inputs.
    check_out1_all_inputs_and: assert property (
        @(posedge clk) out1 == (in1 & in2 & in3 & in4 & in5 & in6 & in7 & in8 & in9)
    );
endmodule