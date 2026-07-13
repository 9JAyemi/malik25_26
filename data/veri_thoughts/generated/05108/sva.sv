module glitch_free_clock_mux_sva #(
    parameter n = 4
) (
    input logic [n-1:0] clk,
    input logic         clk_out,
    input logic [n-1:0] sync_clk1,
    input logic [n-1:0] sync_clk2,
    input logic [n-1:0] sync_clk3,
    input logic [n-1:0] sync_clk4,
    input logic [n-1:0] next_sync_clk,
    input logic [n-1:0] select
);

    // sync_clk1 captures the full clk vector on clk[0].
    check_sync_clk1_capture: assert property (
        @(posedge clk[0]) 1'b1 |=> (sync_clk1 === $past(clk))
    );

    // sync_clk2 captures the full clk vector on clk[1].
    check_sync_clk2_capture: assert property (
        @(posedge clk[1]) 1'b1 |=> (sync_clk2 === $past(clk))
    );

    // sync_clk3 captures the full clk vector on clk[2].
    check_sync_clk3_capture: assert property (
        @(posedge clk[2]) 1'b1 |=> (sync_clk3 === $past(clk))
    );

    // sync_clk4 captures the full clk vector on clk[3].
    check_sync_clk4_capture: assert property (
        @(posedge clk[3]) 1'b1 |=> (sync_clk4 === $past(clk))
    );

    // select chooses sync_clk1 when the decode value is 0000.
    check_select_case_0000: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3])
        (sync_clk1[n-1:n-4] === 4'b0000) |-> (select === sync_clk1)
    );

    // select chooses sync_clk2 when the decode value is 0001.
    check_select_case_0001: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3])
        (sync_clk1[n-1:n-4] === 4'b0001) |-> (select === sync_clk2)
    );

    // select chooses sync_clk3 when the decode value is 0010.
    check_select_case_0010: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3])
        (sync_clk1[n-1:n-4] === 4'b0010) |-> (select === sync_clk3)
    );

    // select chooses sync_clk4 when the decode value is 0011.
    check_select_case_0011: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3])
        (sync_clk1[n-1:n-4] === 4'b0011) |-> (select === sync_clk4)
    );

    // select defaults to sync_clk1 for all other decode values.
    check_select_default: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3])
        ((sync_clk1[n-1:n-4] !== 4'b0000) &&
         (sync_clk1[n-1:n-4] !== 4'b0001) &&
         (sync_clk1[n-1:n-4] !== 4'b0010) &&
         (sync_clk1[n-1:n-4] !== 4'b0011)) |-> (select === sync_clk1)
    );

    // next_sync_clk captures select on a rising edge of select[n-1].
    check_next_sync_clk_capture: assert property (
        @(posedge select[n-1]) 1'b1 |=> (next_sync_clk === $past(select))
    );

    // clk_out matches the implemented combinational expression.
    check_clk_out_function: assert property (
        @(posedge clk[0] or posedge select[n-1])
        (clk_out === ((next_sync_clk[n-1] & ~sync_clk1[n-1]) |
                      (~next_sync_clk[n-1] &  sync_clk1[n-1])))
    );

endmodule