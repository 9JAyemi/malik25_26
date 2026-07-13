module top_module_sva (
    input logic [2:0] in_vec1,
    input logic [2:0] in_vec2,
    input logic sel_b1,   // clock
    input logic sel_b2,
    input logic [2:0] out_vec,
    input logic even_parity
);
    // Clock: sel_b1 (posedge). No reset.
    // Logic: mixed (sequential shift_reg on sel_b1; outputs are combinational).
    // Behavior: out_vec = { (sel_b2 ? in_vec2[1:0] : in_vec1[1:0]), 1'b1 }; even_parity = 1.

    // even_parity output is constant HIGH.
    check_even_parity_const_high: assert property (
        @(posedge sel_b1) even_parity == 1'b1
    );

    // out_vec LSB is always 1.
    check_out_lsb_is_one: assert property (
        @(posedge sel_b1) out_vec[0] == 1'b1
    );

    // Upper two bits of out_vec follow the selected input's [1:0].
    check_out_upper_bits_mux_function: assert property (
        @(posedge sel_b1) out_vec[2:1] == (sel_b2 ? in_vec2[1:0] : in_vec1[1:0])
    );

    // When sel_b2 is HIGH, out_vec[2:1] equals in_vec2[1:0].
    check_sel_high_path_upper_bits: assert property (
        @(posedge sel_b1) sel_b2 |-> (out_vec[2:1] == in_vec2[1:0])
    );

    // When sel_b2 is LOW, out_vec[2:1] equals in_vec1[1:0].
    check_sel_low_path_upper_bits: assert property (
        @(posedge sel_b1) !sel_b2 |-> (out_vec[2:1] == in_vec1[1:0])
    );

    // Full out_vec equals concat of selected [1:0] with trailing 1.
    check_out_vec_full_concat: assert property (
        @(posedge sel_b1) out_vec == { (sel_b2 ? in_vec2[1:0] : in_vec1[1:0]), 1'b1 }
    );

endmodule