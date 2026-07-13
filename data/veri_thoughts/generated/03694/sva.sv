module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic [1:0] select,
    input logic [2:0] mux_in,
    input logic out_comb_ff,
    input logic [3:0] mux_out,
    input logic out_final
);

    // XOR output matches the two input bits.
    check_xor_output: assert property (
        @(posedge clk) out_comb_ff == (a ^ b)
    );

    // Mux output matches the select==00 mapping.
    check_mux_select_00: assert property (
        @(posedge clk) (select == 2'b00) |-> (mux_out == {1'b0, mux_in[2:1]})
    );

    // Mux output matches the select==01 mapping.
    check_mux_select_01: assert property (
        @(posedge clk) (select == 2'b01) |-> (mux_out == {1'b0, mux_in[1:0], 1'b0})
    );

    // Mux output matches the select==10 mapping.
    check_mux_select_10: assert property (
        @(posedge clk) (select == 2'b10) |-> (mux_out == {mux_in[2], 1'b0, mux_in[0]})
    );

    // Mux output matches the select==11 mapping.
    check_mux_select_11: assert property (
        @(posedge clk) (select == 2'b11) |-> (mux_out == {mux_in[2:0], 1'b0})
    );

    // A 0001 mux output causes out_final to capture the XOR result.
    check_out_final_capture_xor: assert property (
        @(posedge clk) (mux_out == 4'b0001) |=> (out_final == $past(out_comb_ff))
    );

    // A 0010 mux output causes out_final to capture the inverted XOR result.
    check_out_final_capture_inv_xor: assert property (
        @(posedge clk) (mux_out == 4'b0010) |=> (out_final == ~$past(out_comb_ff))
    );

    // A 0100 mux output causes out_final to become 0.
    check_out_final_force_zero: assert property (
        @(posedge clk) (mux_out == 4'b0100) |=> (out_final == 1'b0)
    );

    // A 1000 mux output causes out_final to become 1.
    check_out_final_force_one: assert property (
        @(posedge clk) (mux_out == 4'b1000) |=> (out_final == 1'b1)
    );

    // Any other mux output leaves out_final unchanged.
    check_out_final_hold_unmatched: assert property (
        @(posedge clk)
        (mux_out != 4'b0001 && mux_out != 4'b0010 && mux_out != 4'b0100 && mux_out != 4'b1000)
        |=> (out_final == $past(out_final))
    );

endmodule