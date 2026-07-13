module flip_flop_sva (
    input logic clk,
    input logic rst,
    input logic data,
    input logic q,
    input logic q_bar,
    input logic [1:0] type // 0=D, 1=JK, 2=T, 3=SR
);

// Reset drives q=1 and q_bar=0 for all types.
    check_reset_defaults: assert property (
        @(posedge clk) rst |-> (q == 1'b1) && (q_bar == 1'b0)
    );

// D-type: next q equals data, next q_bar equals ~data.
    check_d_type_behavior: assert property (
        @(posedge clk) disable iff (rst)
        (type == 2'b00) |-> ##1 (q == $past(data)) && (q_bar == ~$past(data))
    );

// JK-type: next q equals ~q_bar when data=1, else holds; next q_bar equals ~q when data=1, else holds.
    check_jk_type_behavior: assert property (
        @(posedge clk) disable iff (rst)
        (type == 2'b01) |-> ##1 (
            (data == 1'b1) ? (q == ~$past(q_bar)) && (q_bar == ~$past(q)) : (q == $past(q)) && (q_bar == $past(q_bar))
        )
    );

// T-type: next q equals ~q when data=1, else holds; next q_bar equals ~q_bar when data=1, else holds.
    check_t_type_behavior: assert property (
        @(posedge clk) disable iff (rst)
        (type == 2'b10) |-> ##1 (
            (data == 1'b1) ? (q == ~$past(q)) && (q_bar == ~$past(q_bar)) : (q == $past(q)) && (q_bar == $past(q_bar))
        )
    );

// SR-type: next q equals 0 when data=1, else holds; next q_bar equals 1 when data=1, else holds.
    check_sr_type_behavior: assert property (
        @(posedge clk) disable iff (rst)
        (type == 2'b11) |-> ##1 (
            (data == 1'b1) ? (q == 1'b0) && (q_bar == 1'b1) : (q == $past(q)) && (q_bar == $past(q_bar))
        )
    );

endmodule
