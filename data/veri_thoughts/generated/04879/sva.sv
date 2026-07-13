module top_module_sva (
    input logic clk,
    input logic [31:0] in,
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [3:0] out,
    input logic [31:0] byte_order_rev_out,
    input logic [3:0] mux_out,
    input logic [31:0] sum_out
);

    // Combinational DUT sampled on clk; no reset in the RTL.

    // Byte reversal swaps the four input bytes.
    check_byte_order_reverse: assert property (
        @(posedge clk) byte_order_rev_out === {in[7:0], in[15:8], in[23:16], in[31:24]}
    );

    // sel 000 selects data0.
    check_mux_select_data0: assert property (
        @(posedge clk) (sel === 3'b000) |-> (mux_out === data0)
    );

    // sel 001 selects data1.
    check_mux_select_data1: assert property (
        @(posedge clk) (sel === 3'b001) |-> (mux_out === data1)
    );

    // sel 010 selects data2.
    check_mux_select_data2: assert property (
        @(posedge clk) (sel === 3'b010) |-> (mux_out === data2)
    );

    // sel 011 selects data3.
    check_mux_select_data3: assert property (
        @(posedge clk) (sel === 3'b011) |-> (mux_out === data3)
    );

    // sel 100 selects data4.
    check_mux_select_data4: assert property (
        @(posedge clk) (sel === 3'b100) |-> (mux_out === data4)
    );

    // sel 101 selects data5.
    check_mux_select_data5: assert property (
        @(posedge clk) (sel === 3'b101) |-> (mux_out === data5)
    );

    // Unused select values drive zero.
    check_mux_invalid_select_defaults_zero: assert property (
        @(posedge clk)
        ((sel !== 3'b000) && (sel !== 3'b001) && (sel !== 3'b010) &&
         (sel !== 3'b011) && (sel !== 3'b100) && (sel !== 3'b101))
        |-> (mux_out === 4'b0000)
    );

    // The sum adds the reversed word to the zero-extended mux output.
    check_sum_module_addition: assert property (
        @(posedge clk) sum_out === (byte_order_rev_out + {28'b0, mux_out})
    );

    // The top output is the low nibble of the sum.
    check_top_output_low_nibble: assert property (
        @(posedge clk) out === sum_out[3:0]
    );

endmodule