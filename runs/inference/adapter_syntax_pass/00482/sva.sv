module binary_multiplier_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [7:0] out
);

    // out must equal the sum of the selected power-of-two terms.
    check_out_matches_selected_terms: assert property (
        @(posedge clk)
        out == ((a[0] & b) ? 8'd1 : 8'd0) +
               ((a[1] & b) ? 8'd2 : 8'd0) +
               ((a[2] & b) ? 8'd4 : 8'd0) +
               ((a[3] & b) ? 8'd8 : 8'd0)
    );

    // If a[0] is selected, out must be 1.
    check_a0_selected_sets_out_to_one: assert property (
        @(posedge clk)
        (a[0] & b) |-> (out == 8'd1)
    );

    // If a[1] is selected, out must be 2.
    check_a1_selected_sets_out_to_two: assert property (
        @(posedge clk)
        (a[1] & b) |-> (out == 8'd2)
    );

    // If a[2] is selected, out must be 4.
    check_a2_selected_sets_out_to_four: assert property (
        @(posedge clk)
        (a[2] & b) |-> (out == 8'd4)
    );

    // If a[3] is selected, out must be 8.
    check_a3_selected_sets_out_to_eight: assert property (
        @(posedge clk)
        (a[3] & b) |-> (out == 8'd8)
    );

    // If no bits are selected, out must be 0.
    check_no_selected_bits_sets_out_to_zero: assert property (
        @(posedge clk)
        !(a[0] & b) && !(a[1] & b) && !(a[2] & b) && !(a[3] & b) |-> (out == 8'd0)
    );

    // If only a[0] and a[1] are selected, out must be 3.
    check_a0_a1_selected_sets_out_to_three: assert property (
        @(posedge clk)
        (a[0] & b) && (a[1] & b) && !(a[2] & b) && !(a[3] & b) |-> (out == 8'd3)
    );

    // If only a[0] and a[2] are selected, out must be 5.
    check_a0_a2_selected_sets_out_to_five: assert property (
        @(posedge clk)
        (a[0] & b) && !(a[1] & b) && (a[2] & b) && !(a[3] & b) |-> (out == 8'd5)
    );

    // If only a[0] and a[3] are selected, out must be 9.
    check_a0_a3_selected_sets_out_to_nine: assert property (
        @(posedge clk)
        (a[0] & b) && !(a[1] & b) && !(a[2] & b) && (a[3] & b) |-> (out == 8'd9)
    );

    // If only a[1] and a[2] are selected, out must be 6.
    check_a1_a2_selected_sets_out_to_six: assert property (
        @(posedge clk)
        !(a[0] & b) && (a[1] & b) && (a[2] & b) && !(a[3] & b) |-> (out == 8'd6)
    );

    // If only a[1] and a[3] are selected, out must be 10.
    check_a1_a3_selected_sets_out_to_ten: assert property (
        @(posedge clk)
        !(a[0] & b) && (a[1] & b) && !(a[2] & b) && (a[3] & b) |-> (out == 8'd10)
    );

    // If only a[2] and a[3] are selected, out must be 12.
    check_a2_a3_selected_sets_out_to_twelve: assert property (
        @(posedge clk)
        !(a[0] & b) && !(a[1] & b) && (a[2] & b) && (a[3] & b) |-> (out == 8'd12)
    );

    // If all bits are selected, out must be 15.
    check_all_bits_selected_sets_out_to_fifteen: assert property (
        @(posedge clk)
        (a[0] & b) && (a[1] & b) && (a[2] & b) && (a[3] & b) |-> (out == 8'd15)
    );

endmodule