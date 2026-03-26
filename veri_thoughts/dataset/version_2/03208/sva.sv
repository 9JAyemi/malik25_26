module Span12Mux_s4_h_sva (
    input logic        clk,
    input logic [11:0] I,
    input logic [3:0]  S,
    input logic        O
);

    // Output matches the implemented mux equation.
    check_output_matches_mux_equation: assert property (
        @(posedge clk) disable iff (1'b0)
        O == (((S == 4'b0000) ? I[0] : 1'b0) |
              ((S == 4'b0001) ? I[1] : 1'b0) |
              ((S == 4'b0010) ? I[2] : 1'b0) |
              ((S == 4'b0011) ? I[3] : 1'b0))
    );

    // Select code 0 forwards I[0].
    check_select_0_forwards_i0: assert property (
        @(posedge clk) disable iff (1'b0)
        (S == 4'b0000) |-> (O == I[0])
    );

    // Select code 1 forwards I[1].
    check_select_1_forwards_i1: assert property (
        @(posedge clk) disable iff (1'b0)
        (S == 4'b0001) |-> (O == I[1])
    );

    // Select code 2 forwards I[2].
    check_select_2_forwards_i2: assert property (
        @(posedge clk) disable iff (1'b0)
        (S == 4'b0010) |-> (O == I[2])
    );

    // Select code 3 forwards I[3].
    check_select_3_forwards_i3: assert property (
        @(posedge clk) disable iff (1'b0)
        (S == 4'b0011) |-> (O == I[3])
    );

    // Unused select codes force the output low.
    check_unused_selects_drive_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        (S > 4'd3) |-> (O == 1'b0)
    );

    // A high output must come from the selected low four input bits.
    check_output_high_has_valid_source: assert property (
        @(posedge clk) disable iff (1'b0)
        O |-> (((S == 4'b0000) && I[0]) ||
               ((S == 4'b0001) && I[1]) ||
               ((S == 4'b0010) && I[2]) ||
               ((S == 4'b0011) && I[3]))
    );

endmodule