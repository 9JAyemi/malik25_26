module top_module_sva (
    input logic clk,
    input logic [7:0] d,
    input logic sel,
    input logic [7:0] q,
    input logic [7:0] q_int,
    input logic [3:0] dff_sel
);

    // q_int shifts left and captures d[0] on each falling clock edge.
    check_qint_shift_register: assert property (
        @(negedge clk) 1'b1 |=> q_int == {$past(q_int[6:0]), $past(d[0])}
    );

    // dff_sel increments by one when sel is high.
    check_dff_sel_increment: assert property (
        @(negedge clk) sel |=> dff_sel == ($past(dff_sel) + 4'd1)
    );

    // dff_sel decrements by one when sel is low.
    check_dff_sel_decrement: assert property (
        @(negedge clk) !sel |=> dff_sel == ($past(dff_sel) - 4'd1)
    );

    // q passes q_int through when dff_sel[3] is high.
    check_q_passthrough_when_msb_set: assert property (
        @(posedge clk) dff_sel[3] |-> q == {q_int[7:4], q_int[3:0]}
    );

    // q swaps the q_int nibbles when dff_sel[3] is low.
    check_q_nibble_swap_when_msb_clear: assert property (
        @(posedge clk) !dff_sel[3] |-> q == {q_int[3:0], q_int[7:4]}
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (
    .clk(clk),
    .d(d),
    .sel(sel),
    .q(q),
    .q_int(q_int),
    .dff_sel(dff_sel)
);