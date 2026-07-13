module float_add_sub_altpriority_encoder_v28_sva (
    input logic clk,
    input logic [7:0] data,
    input logic [2:0] q
);

    // No RTL clock/reset; sample combinational behavior on clk.

    // q[2] indicates whether the lower nibble is all zero.
    check_lower_zero_flag: assert property (
        @(posedge clk) q[2] == !(|data[3:0])
    );

    // When the lower nibble is zero, q[1:0] comes from the upper nibble pairs.
    check_upper_pairs_selected_when_lower_zero: assert property (
        @(posedge clk) (!(|data[3:0])) |-> (q[1:0] == {(|data[7:6]), (|data[5:4])})
    );

    // When the lower nibble is nonzero, q[1:0] comes from the lower nibble pairs.
    check_lower_pairs_selected_when_lower_nonzero: assert property (
        @(posedge clk) (|data[3:0]) |-> (q[1:0] == {(|data[3:2]), (|data[1:0])})
    );

    // q[0] matches the selected low pair OR result.
    check_q0_selected_pair_or: assert property (
        @(posedge clk) q[0] == ((!(|data[3:0])) ? (|data[5:4]) : (|data[1:0]))
    );

    // q[1] matches the selected high pair OR result.
    check_q1_selected_pair_or: assert property (
        @(posedge clk) q[1] == ((!(|data[3:0])) ? (|data[7:6]) : (|data[3:2]))
    );

    // All-zero input produces the lower-zero indication and zero pair bits.
    check_all_zero_output: assert property (
        @(posedge clk) (data == 8'h00) |-> (q == 3'b100)
    );

    // Any set input bit must set at least one of the encoded pair bits.
    check_nonzero_input_sets_pair_code: assert property (
        @(posedge clk) (|data[7:0]) |-> (|q[1:0])
    );

    // q matches the complete combinational expression implemented in the RTL.
    check_full_output_expression: assert property (
        @(posedge clk) q == {(!(|data[3:0])), ((!(|data[3:0])) ? {(|data[7:6]), (|data[5:4])} : {(|data[3:2]), (|data[1:0])})}
    );

endmodule