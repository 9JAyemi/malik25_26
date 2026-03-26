module matrix_multiplier_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] matrix1,
    input logic [15:0] matrix2,
    input logic [15:0] result
);

    function automatic [15:0] rtl_temp0;
        input [15:0] m1;
        input [15:0] m2;
        begin
            rtl_temp0 = (m1[3:0]   * m2[0])  +
                        (m1[7:4]   * m2[4])  +
                        (m1[11:8]  * m2[8])  +
                        (m1[15:12] * m2[12]);
        end
    endfunction

    // Result reflects the prior cycle temp[0] computation.
    check_result_matches_temp0: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> result == rtl_temp0($past(matrix1), $past(matrix2))
    );

    // After reset deasserts, the visible result is cleared.
    check_result_clears_on_reset_release: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> result == 16'd0
    );

    // No selected matrix2 bits means the next result is zero.
    check_zero_select_bits_yield_zero: assert property (
        @(posedge clk) disable iff (reset)
        (!matrix2[0] && !matrix2[4] && !matrix2[8] && !matrix2[12]) |=> result == 16'd0
    );

    // A zero matrix1 input drives the next result to zero.
    check_zero_matrix1_yields_zero: assert property (
        @(posedge clk) disable iff (reset)
        (matrix1 == 16'd0) |=> result == 16'd0
    );

    // Selecting only matrix2[0] passes matrix1[3:0] into the next result.
    check_select_bit0_maps_nibble0: assert property (
        @(posedge clk) disable iff (reset)
        (matrix2[0] && !matrix2[4] && !matrix2[8] && !matrix2[12]) |=> result == {12'd0, $past(matrix1[3:0])}
    );

    // Selecting only matrix2[4] passes matrix1[7:4] into the next result.
    check_select_bit4_maps_nibble1: assert property (
        @(posedge clk) disable iff (reset)
        (!matrix2[0] && matrix2[4] && !matrix2[8] && !matrix2[12]) |=> result == {12'd0, $past(matrix1[7:4])}
    );

    // Selecting only matrix2[8] passes matrix1[11:8] into the next result.
    check_select_bit8_maps_nibble2: assert property (
        @(posedge clk) disable iff (reset)
        (!matrix2[0] && !matrix2[4] && matrix2[8] && !matrix2[12]) |=> result == {12'd0, $past(matrix1[11:8])}
    );

    // Selecting only matrix2[12] passes matrix1[15:12] into the next result.
    check_select_bit12_maps_nibble3: assert property (
        @(posedge clk) disable iff (reset)
        (!matrix2[0] && !matrix2[4] && !matrix2[8] && matrix2[12]) |=> result == {12'd0, $past(matrix1[15:12])}
    );

endmodule