module parity_checker_sva (
    input logic clk,
    input logic [7:0] data_in,
    input logic sel_b1,
    input logic parity
);

// When sel_b1 is low, parity matches the XOR of data_in bits.
    check_sel_low_function: assert property (
        @(posedge clk) !sel_b1 |-> (parity == data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7])
    );

// When sel_b1 is high, parity is the inverted XOR of data_in bits.
    check_sel_high_function: assert property (
        @(posedge clk) sel_b1 |-> (parity == ~(data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7]))
    );

// Parity is always the selected parity function of the input bits.
    check_selected_parity_function: assert property (
        @(posedge clk) parity == (sel_b1 ? ~(data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7]) : (data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7]))
    );

endmodule
