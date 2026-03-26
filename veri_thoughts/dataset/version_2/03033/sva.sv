module dual_edge_ff_sva (
    input logic       clk,
    input logic       reset,
    input logic       d,
    input logic       select,
    input logic       q,
    input logic [1:0] ff_out,
    input logic       select_ff
);

    // Reset clears both internal stages.
    check_ff_out_reset: assert property (
        @(posedge clk) reset |=> (ff_out == 2'b00)
    );

    // The low stage captures d on each rising edge.
    check_ff_out_lsb_captures_d: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (ff_out[0] == $past(d))
    );

    // The high stage shifts in the previous low stage.
    check_ff_out_msb_shifts_lsb: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (ff_out[1] == $past(ff_out[0]))
    );

    // select_ff reflects the selected internal stage.
    check_select_ff_mux: assert property (
        @(negedge clk) disable iff (reset) (select_ff == (select ? ff_out[1] : ff_out[0]))
    );

    // q captures select_ff on each falling edge.
    check_q_captures_select_ff: assert property (
        @(negedge clk) disable iff (reset) 1'b1 |=> (q == $past(select_ff))
    );

endmodule