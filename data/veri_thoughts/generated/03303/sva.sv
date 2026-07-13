module top_module_sva (
    input logic        clk,
    input logic [2:0]  sel,
    input logic [3:0]  data0,
    input logic [3:0]  data1,
    input logic [3:0]  data2,
    input logic [3:0]  data3,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic [7:0]  c,
    input logic [7:0]  d,
    input logic [7:0]  sum
);

    function automatic [3:0] exp_mux_out (
        input logic [2:0] sel_f,
        input logic [3:0] data0_f,
        input logic [3:0] data1_f,
        input logic [3:0] data2_f,
        input logic [3:0] data3_f
    );
    begin
        case (sel_f)
            3'b000: exp_mux_out = data0_f;
            3'b001: exp_mux_out = data1_f;
            3'b010: exp_mux_out = data2_f;
            3'b011: exp_mux_out = data3_f;
            default: exp_mux_out = 4'b0000;
        endcase
    end
    endfunction

    function automatic [1:0] exp_min_index (
        input logic [7:0] a_f,
        input logic [7:0] b_f,
        input logic [7:0] c_f,
        input logic [7:0] d_f
    );
    begin
        if ((a_f <= b_f) && (a_f <= c_f) && (a_f <= d_f))
            exp_min_index = 2'b00;
        else if ((b_f <= c_f) && (b_f <= d_f))
            exp_min_index = 2'b01;
        else if (c_f <= d_f)
            exp_min_index = 2'b10;
        else
            exp_min_index = 2'b11;
    end
    endfunction

    function automatic [7:0] exp_sum_from_parts (
        input logic [3:0] mux_f,
        input logic [1:0] min_f
    );
        logic [3:0] add_f;
    begin
        add_f = mux_f + min_f;
        exp_sum_from_parts = {4'b0000, add_f};
    end
    endfunction

    function automatic [7:0] exp_sum (
        input logic [2:0] sel_f,
        input logic [3:0] data0_f,
        input logic [3:0] data1_f,
        input logic [3:0] data2_f,
        input logic [3:0] data3_f,
        input logic [7:0] a_f,
        input logic [7:0] b_f,
        input logic [7:0] c_f,
        input logic [7:0] d_f
    );
        logic [3:0] mux_f;
        logic [1:0] min_f;
    begin
        mux_f   = exp_mux_out(sel_f, data0_f, data1_f, data2_f, data3_f);
        min_f   = exp_min_index(a_f, b_f, c_f, d_f);
        exp_sum = exp_sum_from_parts(mux_f, min_f);
    end
    endfunction

    // Sum matches the implemented mux-plus-min-index function.
    check_sum_matches_combined_logic: assert property (
        @(posedge clk) sum == exp_sum(sel, data0, data1, data2, data3, a, b, c, d)
    );

    // The upper nibble of sum is always zero because the addition is 4 bits wide.
    check_sum_upper_bits_zero: assert property (
        @(posedge clk) sum[7:4] == 4'b0000
    );

    // sel 000 selects data0 into the adder.
    check_sel_000_uses_data0: assert property (
        @(posedge clk) (sel == 3'b000) |-> (sum == exp_sum_from_parts(data0, exp_min_index(a, b, c, d)))
    );

    // sel 001 selects data1 into the adder.
    check_sel_001_uses_data1: assert property (
        @(posedge clk) (sel == 3'b001) |-> (sum == exp_sum_from_parts(data1, exp_min_index(a, b, c, d)))
    );

    // sel 010 selects data2 into the adder.
    check_sel_010_uses_data2: assert property (
        @(posedge clk) (sel == 3'b010) |-> (sum == exp_sum_from_parts(data2, exp_min_index(a, b, c, d)))
    );

    // sel 011 selects data3 into the adder.
    check_sel_011_uses_data3: assert property (
        @(posedge clk) (sel == 3'b011) |-> (sum == exp_sum_from_parts(data3, exp_min_index(a, b, c, d)))
    );

    // sel values 100 through 111 force the mux contribution to zero.
    check_sel_default_zeros_mux: assert property (
        @(posedge clk) sel[2] |-> (sum == exp_sum_from_parts(4'b0000, exp_min_index(a, b, c, d)))
    );

    // When a is minimal or tied for minimal, the encoded index is 0.
    check_a_priority_when_a_is_min: assert property (
        @(posedge clk) ((a <= b) && (a <= c) && (a <= d)) |-> (sum == exp_sum_from_parts(exp_mux_out(sel, data0, data1, data2, data3), 2'b00))
    );

    // When a is not minimal and b is minimal or tied, the encoded index is 1.
    check_b_priority_when_b_is_min: assert property (
        @(posedge clk) (!((a <= b) && (a <= c) && (a <= d)) && ((b <= c) && (b <= d))) |-> (sum == exp_sum_from_parts(exp_mux_out(sel, data0, data1, data2, data3), 2'b01))
    );

    // When a and b are not minimal and c is less than or equal to d, the encoded index is 2.
    check_c_priority_when_c_is_min: assert property (
        @(posedge clk) (!((a <= b) && (a <= c) && (a <= d)) && !((b <= c) && (b <= d)) && (c <= d)) |-> (sum == exp_sum_from_parts(exp_mux_out(sel, data0, data1, data2, data3), 2'b10))
    );

    // When d is the remaining minimum case, the encoded index is 3.
    check_d_selected_when_only_d_is_min: assert property (
        @(posedge clk) (!((a <= b) && (a <= c) && (a <= d)) && !((b <= c) && (b <= d)) && !(c <= d)) |-> (sum == exp_sum_from_parts(exp_mux_out(sel, data0, data1, data2, data3), 2'b11))
    );

endmodule