module top_module_sva (
    input logic CLK,
    input logic RESETn,
    // DUT ports
    input logic [3:0] in,
    input logic [1:0] pos,
    input logic       all_high,
    // Internal signals from DUT
    input logic [1:0] pos_wire,
    input logic       is_zero
);
    ///// priority_encoder behavior /////
    // Zero input -> pos_wire=00 and is_zero=1.
    pe_zero_input_outputs: assert property (
        @(posedge CLK) disable iff (!RESETn) (in == 4'b0000) |-> (pos_wire == 2'b00) && (is_zero == 1'b1)
    );
    // Nonzero input -> is_zero=0 and pos_wire duplicates MSB.
    pe_nonzero_input_outputs: assert property (
        @(posedge CLK) disable iff (!RESETn) (in != 4'b0000) |-> (is_zero == 1'b0) && (pos_wire == {2{in[3]}})
    );
    // MSB high -> pos_wire=11 and is_zero=0.
    pe_msb_high_pos_11: assert property (
        @(posedge CLK) disable iff (!RESETn) (in[3] == 1'b1) |-> (pos_wire == 2'b11) && (is_zero == 1'b0)
    );
    // Nonzero with MSB low -> pos_wire=00 and is_zero=0.
    pe_nonzero_msb_low_pos_00: assert property (
        @(posedge CLK) disable iff (!RESETn) ((in != 4'b0000) && (in[3] == 1'b0)) |-> (pos_wire == 2'b00) && (is_zero == 1'b0)
    );
    // is_zero is exactly (in == 0).
    pe_is_zero_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn) (is_zero == (in == 4'b0000))
    );
    // When is_zero=1, pos_wire must be 00.
    pe_is_zero_implies_pos00: assert property (
        @(posedge CLK) disable iff (!RESETn) is_zero |-> (pos_wire == 2'b00)
    );
    // pos bits are always equal (00 or 11).
    pe_pos_bits_equal: assert property (
        @(posedge CLK) disable iff (!RESETn) (pos_wire[1] == pos_wire[0])
    );

    ///// top_module wiring /////
    // Top-level pos mirrors internal pos_wire.
    top_pos_matches_internal: assert property (
        @(posedge CLK) disable iff (!RESETn) (pos == pos_wire)
    );
    // Top-level pos bits are equal (propagated from pos_wire).
    top_pos_bits_equal: assert property (
        @(posedge CLK) disable iff (!RESETn) (pos[1] == pos[0])
    );

    ///// and_gate behavior /////
    // all_high equals (is_zero ? 0 : (in == 4'hF)).
    ag_all_high_definition: assert property (
        @(posedge CLK) disable iff (!RESETn) ( all_high == (is_zero ? 1'b0 : (in == 4'b1111)) )
    );
    // all_high implies in==1111 and not is_zero.
    ag_all_high_implies_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn) all_high |-> (!is_zero) && (in == 4'b1111)
    );
    // is_zero forces all_high to 0.
    ag_is_zero_clears_all_high: assert property (
        @(posedge CLK) disable iff (!RESETn) is_zero |-> (all_high == 1'b0)
    );
    // For in==1111, outputs are consistent: is_zero=0, pos_wire=11, all_high=1.
    ag_full_one_vector_consistency: assert property (
        @(posedge CLK) disable iff (!RESETn) (in == 4'b1111) |-> (is_zero == 1'b0) && (pos_wire == 2'b11) && (all_high == 1'b1)
    );
endmodule