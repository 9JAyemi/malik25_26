module top_module_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [7:0] out,
    input logic [2:0] pos,
    input logic [7:0] out_hi,
    input logic [7:0] out_lo,
    input logic select
);
    ///// Combinational submodule behavior /////
    // word_splitter high byte is always zero (input upper 8 bits are zero).
    check_out_hi_zero: assert property (
        @(posedge clk) out_hi == 8'h00
    );
    // word_splitter low byte equals input.
    check_out_lo_eq_in: assert property (
        @(posedge clk) out_lo == in
    );

    ///// priority_encoder mapping /////
    // pos mapping for one-hot bit0.
    pe_map_b0: assert property (
        @(posedge clk) (in == 8'b00000001) |-> (pos == 3'b000)
    );
    // pos mapping for one-hot bit1.
    pe_map_b1: assert property (
        @(posedge clk) (in == 8'b00000010) |-> (pos == 3'b001)
    );
    // pos mapping for one-hot bit2.
    pe_map_b2: assert property (
        @(posedge clk) (in == 8'b00000100) |-> (pos == 3'b010)
    );
    // pos mapping for one-hot bit3.
    pe_map_b3: assert property (
        @(posedge clk) (in == 8'b00001000) |-> (pos == 3'b011)
    );
    // pos mapping for one-hot bit4.
    pe_map_b4: assert property (
        @(posedge clk) (in == 8'b00010000) |-> (pos == 3'b100)
    );
    // pos mapping for one-hot bit5.
    pe_map_b5: assert property (
        @(posedge clk) (in == 8'b00100000) |-> (pos == 3'b101)
    );
    // pos mapping for one-hot bit6.
    pe_map_b6: assert property (
        @(posedge clk) (in == 8'b01000000) |-> (pos == 3'b110)
    );
    // pos mapping for one-hot bit7.
    pe_map_b7: assert property (
        @(posedge clk) (in == 8'b10000000) |-> (pos == 3'b111)
    );
    // Default: for non-one-hot (including zero), pos is 000.
    pe_default_zero: assert property (
        @(posedge clk) (!(in inside {8'b00000001,8'b00000010,8'b00000100,8'b00001000,8'b00010000,8'b00100000,8'b01000000,8'b10000000})) |-> (pos == 3'b000)
    );

    ///// select derivation from pos /////
    // select is high iff pos != 000.
    select_when_pos_nonzero: assert property (
        @(posedge clk) (pos != 3'b000) |-> (select == 1'b1)
    );
    // select is low iff pos == 000.
    deselect_when_pos_zero: assert property (
        @(posedge clk) (pos == 3'b000) |-> (select == 1'b0)
    );

    ///// Registered mux behavior /////
    // When select is 1, next-cycle out equals previous out_hi.
    mux_select_one: assert property (
        @(posedge clk) select |=> (out == $past(out_hi))
    );
    // When select is 0, next-cycle out equals previous out_lo.
    mux_select_zero: assert property (
        @(posedge clk) !select |=> (out == $past(out_lo))
    );

    ///// End-to-end mapping /////
    // For upper one-hot inputs (bits 1..7), next-cycle out is zero.
    out_zero_for_upper_onehots: assert property (
        @(posedge clk) (in inside {8'b00000010,8'b00000100,8'b00001000,8'b00010000,8'b00100000,8'b01000000,8'b10000000}) |=> (out == 8'h00)
    );
    // For all other inputs, next-cycle out equals previous input.
    out_eq_in_otherwise: assert property (
        @(posedge clk) (!(in inside {8'b00000010,8'b00000100,8'b00001000,8'b00010000,8'b00100000,8'b01000000,8'b10000000})) |=> (out == $past(in))
    );
endmodule