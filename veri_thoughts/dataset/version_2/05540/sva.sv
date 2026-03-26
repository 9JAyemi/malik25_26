module shift_reg_mux_xor_sva (
    input logic clk,
    input logic d,
    input logic [255:0] in,
    input logic [7:0] sel,
    input logic q,
    input logic [2:0] shift_reg,
    input logic [7:0] mux_sel,
    input logic [0:255] mux_out
);

    // shift_reg shifts in d on every rising edge.
    check_shift_reg_update: assert property (
        @(posedge clk) 1'b1 |=> (shift_reg == {$past(shift_reg[1:0]), $past(d)})
    );

    // mux_sel is a direct combinational copy of sel.
    check_mux_sel_passthrough: assert property (
        @(posedge clk) (mux_sel == sel)
    );

    // mux_out index 0 maps to the MSB of in.
    check_mux_out_low_index_boundary: assert property (
        @(posedge clk) (mux_out[8'h00] == in[255])
    );

    // mux_out index 255 maps to the LSB of in.
    check_mux_out_high_index_boundary: assert property (
        @(posedge clk) (mux_out[8'hFF] == in[0])
    );

    // The selected mux bit corresponds to in[255-sel].
    check_mux_selected_bit_mapping: assert property (
        @(posedge clk) (mux_out[mux_sel] == in[8'd255 - sel])
    );

    // q is the XOR of shift_reg[0] and mux_out at mux_sel.
    check_q_xor_implementation: assert property (
        @(posedge clk) (q == (shift_reg[0] ^ mux_out[mux_sel]))
    );

    // q also matches shift_reg[0] XOR the selected bit from in.
    check_q_port_level_mapping: assert property (
        @(posedge clk) (q == (shift_reg[0] ^ in[8'd255 - sel]))
    );

    // One cycle later, q uses the prior sampled d and current selected input bit.
    check_q_end_to_end_behavior: assert property (
        @(posedge clk) 1'b1 |=> (q == ($past(d) ^ in[8'd255 - sel]))
    );

endmodule