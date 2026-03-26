module bit_reversal_sva (
    input logic [7:0] data_in,
    input logic [7:0] data_out
);
    // No RTL clock or reset; use $global_clock for this combinational logic.
    // data_out is data_in with the bit order reversed.
    check_bit_reversal_mapping: assert property (
        @($global_clock)
        data_out == {data_in[0], data_in[1], data_in[2], data_in[3], data_in[4], data_in[5], data_in[6], data_in[7]}
    );
endmodule

module mux_256_to_1_sva (
    input logic [255:0] data_in,
    input logic [7:0] sel,
    input logic [7:0] data_out
);
    // No RTL clock or reset; use $global_clock for this combinational logic.
    // Select 0 returns the lowest byte.
    check_mux_select_0: assert property (
        @($global_clock)
        (sel == 8'd0) |-> (data_out == data_in[7:0])
    );

    // Select 31 returns the highest valid byte.
    check_mux_select_31: assert property (
        @($global_clock)
        (sel == 8'd31) |-> (data_out == data_in[255:248])
    );

    // Valid byte selects 0 through 31 return the addressed 8-bit slice.
    check_mux_valid_select_mapping: assert property (
        @($global_clock)
        (sel <= 8'd31) |-> (data_out == data_in[sel*8 +: 8])
    );
endmodule

module binary_adder_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic sel,
    input logic [7:0] out
);
    // No RTL clock or reset; use $global_clock for this combinational logic.
    // sel low adds a and b directly.
    check_binary_adder_direct_mode: assert property (
        @($global_clock)
        (!sel) |-> (out == (a + b))
    );

    // sel high adds a and the bit-reversed value of b.
    check_binary_adder_reversed_mode: assert property (
        @($global_clock)
        sel |-> (out == (a + {b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]}))
    );
endmodule

bind bit_reversal bit_reversal_sva bit_reversal_sva_bind (
    .data_in(data_in),
    .data_out(data_out)
);

bind mux_256_to_1 mux_256_to_1_sva mux_256_to_1_sva_bind (
    .data_in(data_in),
    .sel(sel),
    .data_out(data_out)
);

bind binary_adder binary_adder_sva binary_adder_sva_bind (
    .a(a),
    .b(b),
    .sel(sel),
    .out(out)
);