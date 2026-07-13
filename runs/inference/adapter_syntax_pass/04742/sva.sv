module dffe_sva #(
    parameter SIZE = 8
)(
    input logic [SIZE-1:0] din,
    input logic en,
    input logic clk,
    input logic [SIZE-1:0] q,
    input logic se,
    input logic [SIZE-1:0] si,
    input logic [SIZE-1:0] so
);

    // so is always driven by q.
    check_so_matches_q: assert property (
        @(posedge clk) so == q
    );

    // When se is high, q loads si on the next cycle.
    check_se_loads_si: assert property (
        @(posedge clk) se |=> (q == $past(si))
    );

    // When se is low and en is high, q loads din on the next cycle.
    check_en_loads_din: assert property (
        @(posedge clk) (!se && en) |=> (q == $past(din))
    );

    // When both se and en are low, q holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge clk) (!se && !en) |=> (q == $past(q))
    );

endmodule