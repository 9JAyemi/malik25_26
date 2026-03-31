module dffe_sva (
    input logic [7:0] din,
    input logic       en,
    input logic       clk,
    input logic [7:0] q,
    input logic       se,
    input logic [7:0] si,
    input logic [7:0] so
);

// Clock: clk (posedge). Reset: none. Logic: sequential with enable and select.

    // q captures si when se is high.
    check_se_loads_si: assert property (
        @(posedge clk) se |=> (q == $past(si))
    );

// q captures din when se is low and en is high.
    check_en_loads_din: assert property (
        @(posedge clk) (!se && en) |=> (q == $past(din))
    );

// q holds its value when neither select/enable is asserted.
    check_hold_when_idle: assert property (
        @(posedge clk) (!se && !en) |=> (q == $past(q))
    );

// so is always a direct copy of q.
    check_so_is_q: assert property (
        @(posedge clk) (so == q)
    );

endmodule
