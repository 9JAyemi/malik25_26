module right_shift_arithmetic_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [15:0] out,
    input logic [3:0]  shift
);

    // No clock or reset exists in the RTL; sample the combinational logic on clk.

    // Shift 0 passes the input through unchanged.
    check_shift_0_passthrough: assert property (
        @(posedge clk) (shift == 4'd0) |-> (out == in)
    );

    // Shift 1 replicates the sign bit once and shifts right by 1.
    check_shift_1_behavior: assert property (
        @(posedge clk) (shift == 4'd1) |-> (out == {in[15], in[15:1]})
    );

    // Shift 2 replicates the sign bit twice and shifts right by 2.
    check_shift_2_behavior: assert property (
        @(posedge clk) (shift == 4'd2) |-> (out == {{2{in[15]}}, in[15:2]})
    );

    // Shift 3 replicates the sign bit three times and shifts right by 3.
    check_shift_3_behavior: assert property (
        @(posedge clk) (shift == 4'd3) |-> (out == {{3{in[15]}}, in[15:3]})
    );

    // Shift 4 replicates the sign bit four times and shifts right by 4.
    check_shift_4_behavior: assert property (
        @(posedge clk) (shift == 4'd4) |-> (out == {{4{in[15]}}, in[15:4]})
    );

    // Shift 5 replicates the sign bit five times and shifts right by 5.
    check_shift_5_behavior: assert property (
        @(posedge clk) (shift == 4'd5) |-> (out == {{5{in[15]}}, in[15:5]})
    );

    // Shift 6 replicates the sign bit six times and shifts right by 6.
    check_shift_6_behavior: assert property (
        @(posedge clk) (shift == 4'd6) |-> (out == {{6{in[15]}}, in[15:6]})
    );

    // Shift 7 replicates the sign bit seven times and shifts right by 7.
    check_shift_7_behavior: assert property (
        @(posedge clk) (shift == 4'd7) |-> (out == {{7{in[15]}}, in[15:7]})
    );

    // Shift 8 replicates the sign bit eight times and shifts right by 8.
    check_shift_8_behavior: assert property (
        @(posedge clk) (shift == 4'd8) |-> (out == {{8{in[15]}}, in[15:8]})
    );

    // Shift 9 replicates the sign bit nine times and shifts right by 9.
    check_shift_9_behavior: assert property (
        @(posedge clk) (shift == 4'd9) |-> (out == {{9{in[15]}}, in[15:9]})
    );

    // Shift 10 replicates the sign bit ten times and shifts right by 10.
    check_shift_10_behavior: assert property (
        @(posedge clk) (shift == 4'd10) |-> (out == {{10{in[15]}}, in[15:10]})
    );

    // Shift 11 replicates the sign bit eleven times and shifts right by 11.
    check_shift_11_behavior: assert property (
        @(posedge clk) (shift == 4'd11) |-> (out == {{11{in[15]}}, in[15:11]})
    );

    // Shift 12 replicates the sign bit twelve times and shifts right by 12.
    check_shift_12_behavior: assert property (
        @(posedge clk) (shift == 4'd12) |-> (out == {{12{in[15]}}, in[15:12]})
    );

    // Shift 13 replicates the sign bit thirteen times and shifts right by 13.
    check_shift_13_behavior: assert property (
        @(posedge clk) (shift == 4'd13) |-> (out == {{13{in[15]}}, in[15:13]})
    );

    // Shift 14 replicates the sign bit fourteen times and shifts right by 14.
    check_shift_14_behavior: assert property (
        @(posedge clk) (shift == 4'd14) |-> (out == {{14{in[15]}}, in[15:14]})
    );

    // Shift 15 fills the entire output with the input sign bit.
    check_shift_15_behavior: assert property (
        @(posedge clk) (shift == 4'd15) |-> (out == {16{in[15]}})
    );

endmodule