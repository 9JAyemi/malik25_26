module priority_encoder_sva (
    input logic CLK,
    input logic [7:0] a, b, c, d,
    input logic [1:0] index
);
    // If a is non-zero, index selects 00.
    check_index_a_priority: assert property (
        @(posedge CLK) (a != 8'h00) |-> (index == 2'b00)
    );
    // If a is zero and b is non-zero, index selects 01.
    check_index_b_priority_when_a_zero: assert property (
        @(posedge CLK) (a == 8'h00 && b != 8'h00) |-> (index == 2'b01)
    );
    // If a and b are zero and c is non-zero, index selects 10.
    check_index_c_priority_when_a_b_zero: assert property (
        @(posedge CLK) (a == 8'h00 && b == 8'h00 && c != 8'h00) |-> (index == 2'b10)
    );
    // If only d is non-zero (a,b,c zero), index selects 11.
    check_index_d_priority_when_a_b_c_zero: assert property (
        @(posedge CLK) (a == 8'h00 && b == 8'h00 && c == 8'h00 && d != 8'h00) |-> (index == 2'b11)
    );
    // When all inputs are zero, index is 11.
    check_index_when_all_zero: assert property (
        @(posedge CLK) (a == 8'h00 && b == 8'h00 && c == 8'h00 && d == 8'h00) |-> (index == 2'b11)
    );
    // If index is 00, a must be non-zero.
    decode_index_00_implies_a_nonzero: assert property (
        @(posedge CLK) (index == 2'b00) |-> (a != 8'h00)
    );
    // If index is 01, a is zero and b is non-zero.
    decode_index_01_implies_b_nonzero_and_a_zero: assert property (
        @(posedge CLK) (index == 2'b01) |-> (a == 8'h00 && b != 8'h00)
    );
    // If index is 10, a and b are zero and c is non-zero.
    decode_index_10_implies_c_nonzero_and_a_b_zero: assert property (
        @(posedge CLK) (index == 2'b10) |-> (a == 8'h00 && b == 8'h00 && c != 8'h00)
    );
    // If index is 11, a, b, and c are zero (d can be zero or non-zero).
    decode_index_11_implies_a_b_c_zero: assert property (
        @(posedge CLK) (index == 2'b11) |-> (a == 8'h00 && b == 8'h00 && c == 8'h00)
    );
endmodule

module mux_4to1_priority_encoder_sva (
    input logic CLK,
    input logic [7:0] a, b, c, d,
    input logic [1:0] select,
    input logic [7:0] out
);
    // When select==00, out equals a.
    check_mux_sel_00_maps_to_a: assert property (
        @(posedge CLK) (select == 2'b00) |-> (out == a)
    );
    // When select==01, out equals b.
    check_mux_sel_01_maps_to_b: assert property (
        @(posedge CLK) (select == 2'b01) |-> (out == b)
    );
    // When select==10, out equals c.
    check_mux_sel_10_maps_to_c: assert property (
        @(posedge CLK) (select == 2'b10) |-> (out == c)
    );
    // When select==11, out equals d.
    check_mux_sel_11_maps_to_d: assert property (
        @(posedge CLK) (select == 2'b11) |-> (out == d)
    );
endmodule