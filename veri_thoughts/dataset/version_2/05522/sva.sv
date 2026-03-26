module ff_d_sva #(parameter WIDTH = 8) (
    input logic [WIDTH-1:0] D,
    input logic             en,
    input logic             clk,
    input logic             res,
    input logic [WIDTH-1:0] Q
);

    // Synchronous reset clears Q.
    check_reset_clears_q: assert property (
        @(posedge clk) res |=> (Q == {WIDTH{1'b0}})
    );

    // Reset overrides enable when both are high.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (res && en) |=> (Q == {WIDTH{1'b0}})
    );

    // Enable causes Q to capture D.
    check_enable_captures_d: assert property (
        @(posedge clk) disable iff (res) en |=> (Q == $past(D))
    );

    // Without enable, Q holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (res) !en |=> (Q == $past(Q))
    );

endmodule