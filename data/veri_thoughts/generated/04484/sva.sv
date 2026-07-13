module DFF_EN_sva (
    input logic C,
    input logic E,
    input logic S,
    input logic R,
    input logic D,
    input logic Q
);
    // Sequential logic on C; R is an active-high synchronous reset.
    // Reset has highest priority and clears Q.
    dff_en_reset_clears_q: assert property (
        @(posedge C) R |=> (Q == 1'b0)
    );

    // Set drives Q high when reset is low.
    dff_en_set_forces_q_high: assert property (
        @(posedge C) disable iff (R) S |=> (Q == 1'b1)
    );

    // With reset and set low, enabled D=1 loads Q high.
    dff_en_enable_loads_one: assert property (
        @(posedge C) disable iff (R) (!S && (E == 1'b1) && (D == 1'b1)) |=> (Q == 1'b1)
    );

    // With reset and set low, enabled D=0 loads Q low.
    dff_en_enable_loads_zero: assert property (
        @(posedge C) disable iff (R) (!S && (E == 1'b1) && (D == 1'b0)) |=> (Q == 1'b0)
    );

    // With reset and set low, E=0 holds the previous Q value.
    dff_en_disable_holds_q: assert property (
        @(posedge C) disable iff (R) (!S && (E == 1'b0)) |=> (Q == $past(Q))
    );
endmodule

module DFFSR_sva (
    input logic C,
    input logic S,
    input logic R,
    input logic D,
    input logic Q
);
    // Sequential logic on C; R is an active-high synchronous reset.
    // Reset has highest priority and clears Q.
    dffsr_reset_clears_q: assert property (
        @(posedge C) R |=> (Q == 1'b0)
    );

    // Set drives Q high when reset is low.
    dffsr_set_forces_q_high: assert property (
        @(posedge C) disable iff (R) S |=> (Q == 1'b1)
    );

    // With reset and set low, D=1 loads Q high.
    dffsr_loads_one: assert property (
        @(posedge C) disable iff (R) (!S && (D == 1'b1)) |=> (Q == 1'b1)
    );

    // With reset and set low, D=0 loads Q low.
    dffsr_loads_zero: assert property (
        @(posedge C) disable iff (R) (!S && (D == 1'b0)) |=> (Q == 1'b0)
    );
endmodule