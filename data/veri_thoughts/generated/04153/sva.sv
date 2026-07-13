module multiplexer_4to1_sva (
    input logic clk,
    input logic [3:0] a,
    input logic sel_b1,
    input logic sel_b2,
    input logic [3:0] out_always
);

    // Select 00 routes the register pass-through value.
    check_sel_00_routes_register: assert property (
        @(posedge clk)
        (!sel_b2 && !sel_b1) |-> (out_always == a)
    );

    // Select 01 routes the incremented counter value.
    check_sel_01_routes_counter: assert property (
        @(posedge clk)
        (!sel_b2 && sel_b1) |-> (out_always == (a + 4'd1))
    );

    // Select 10 forces the output to zero.
    check_sel_10_drives_zero: assert property (
        @(posedge clk)
        (sel_b2 && !sel_b1) |-> (out_always == 4'b0000)
    );

    // Select 11 forces the output to all ones.
    check_sel_11_drives_ones: assert property (
        @(posedge clk)
        (sel_b2 && sel_b1) |-> (out_always == 4'b1111)
    );

endmodule