module gray_code_state_machine_sva #(
    parameter int n = 4
) (
    input logic clk,
    input logic rst,
    input logic [n-1:0] out
);

    // Reset forces the output low.
    check_reset_clears_output: assert property (
        @(posedge clk) rst |-> (out == '0)
    );

    // State 0 maps to gray code 0.
    check_state_0_maps_to_gray_0: assert property (
        @(posedge clk) disable iff (rst) (out == 1'b0) |-> ($past(out) == 1'b0)
    );

    // State 1 maps to gray code 1.
    check_state_1_maps_to_gray_1: assert property (
        @(posedge clk) disable iff (rst) (out == 1'b1) |-> ($past(out) == 1'b1)
    );

    // State 2 maps to gray code 3.
    check_state_2_maps_to_gray_3: assert property (
        @(posedge clk) disable iff (rst) (out == 3'b11) |-> ($past(out) == 3'b11)
    );

    // State 3 maps to gray code 2.
    check_state_3_maps_to_gray_2: assert property (
        @(posedge clk) disable iff (rst) (out == 3'b10) |-> ($past(out) == 3'b10)
    );

    // State 4 maps to gray code 6.
    check_state_4_maps_to_gray_6: assert property (
        @(posedge clk) disable iff (rst) (out == 3'b110) |-> ($past(out) == 3'b110)
    );

    // State 5 maps to gray code 7.
    check_state_5_maps_to_gray_7: assert property (
        @(posedge clk) disable iff (rst) (out == 3'b111) |-> ($past(out) == 3'b111)
    );

    // State 6 maps to gray code 5.
    check_state_6_maps_to_gray_5: assert property (
        @(posedge clk) disable iff (rst) (out == 3'b101) |-> ($past(out) == 3'b101)
    );

    // State 7 maps to gray code 4.
    check_state_7_maps_to_gray_4: assert property (
        @(posedge clk) disable iff (rst) (out == 3'b100) |-> ($past(out) == 3'b100)
    );

    // All other states map to gray code 0.
    check_default_state_maps_to_gray_0: assert property (
        @(posedge clk) disable iff (rst)
        ((out != 1'b0) && (out != 1'b1) && (out != 3'b11) && (out != 3'b10) &&
         (out != 3'b110) && (out != 3'b111) && (out != 3'b101) && (out != 3'b100))
        |-> ($past(out) == 1'b0)
    );

endmodule