module up_down_counter_sva (
    input logic       UD,
    input logic       RST,
    input logic       clk,
    input logic [3:0] Q,
    input logic       OVF
);

    // Reset forces Q and OVF low.
    check_reset_clears_state: assert property (
        @(posedge clk) !RST |-> ((Q == 4'h0) && (OVF == 1'b0))
    );

    // Counting up below 15 increments Q and clears OVF.
    check_count_up_increment: assert property (
        @(posedge clk) disable iff (!RST)
        (UD && (Q != 4'hF)) |=> ((Q == ($past(Q) + 4'h1)) && (OVF == 1'b0))
    );

    // Counting up at 15 wraps Q to 0 and sets OVF.
    check_count_up_wrap: assert property (
        @(posedge clk) disable iff (!RST)
        (UD && (Q == 4'hF)) |=> ((Q == 4'h0) && (OVF == 1'b1))
    );

    // Counting down above 0 decrements Q and clears OVF.
    check_count_down_decrement: assert property (
        @(posedge clk) disable iff (!RST)
        (!UD && (Q != 4'h0)) |=> ((Q == ($past(Q) - 4'h1)) && (OVF == 1'b0))
    );

    // Counting down at 0 wraps Q to 15 and sets OVF.
    check_count_down_wrap: assert property (
        @(posedge clk) disable iff (!RST)
        (!UD && (Q == 4'h0)) |=> ((Q == 4'hF) && (OVF == 1'b1))
    );

    // Overflow can only appear with a wrapped boundary value.
    check_ovf_implies_boundary_q: assert property (
        @(posedge clk) disable iff (!RST)
        OVF |-> ((Q == 4'h0) || (Q == 4'hF))
    );

    // Midrange counter values must not assert overflow.
    check_midrange_q_has_no_ovf: assert property (
        @(posedge clk) disable iff (!RST)
        ((Q != 4'h0) && (Q != 4'hF)) |-> (OVF == 1'b0)
    );

endmodule