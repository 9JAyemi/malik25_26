module reg_32bits_sva (
    input logic [31:0] d,
    input logic        we,
    input logic        clk,
    input logic        rst,
    input logic [31:0] q
);

    // A sampled reset must leave q cleared by the next clock.
    check_reset_clears_q_next_cycle: assert property (
        @(posedge clk) rst |=> (q == 32'b0)
    );

    // A previously sampled reset keeps q at zero on the following clock.
    check_reset_value_persists: assert property (
        @(posedge clk) (!$initstate && $past(rst)) |-> (q == 32'b0)
    );

    // Any sampled change to a nonzero q must come from a prior write.
    check_nonzero_change_requires_write: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && (q != 32'b0) && (q != $past(q))) |-> ($past(we) && (q == $past(d)))
    );

    // A sampled nonzero q after a prior write must match the written data.
    check_nonzero_write_data_matches_q: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && $past(we) && (q != 32'b0)) |-> (q == $past(d))
    );

    // Without a prior write, a sampled nonzero q must hold its value.
    check_nonzero_holds_without_write: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && !$past(we) && ($past(q) != 32'b0) && (q != 32'b0)) |-> (q == $past(q))
    );

    // Without a prior write, a sampled zero q cannot become nonzero.
    check_zero_cannot_become_nonzero_without_write: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && !$past(we) && ($past(q) == 32'b0)) |-> (q == 32'b0)
    );

endmodule