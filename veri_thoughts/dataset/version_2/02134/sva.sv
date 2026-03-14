module dffrl_async_sva #(
    parameter SIZE = 1
) (
    input  logic [SIZE-1:0] din,
    input  logic            clk,
    input  logic            rst_l,   // active-low async reset
    input  logic [SIZE-1:0] q,
    input  logic            se,
    input  logic [SIZE-1:0] si,
    input  logic [SIZE-1:0] so
);
    // Clock: clk; Reset: rst_l (active-low, asynchronous)
    // Logic: sequential DFF with async reset and scan mux; so mirrors q

    // so must always mirror q (continuous assign)
    so_mirrors_q: assert property (
        @(posedge clk) so == q
    );

    // While reset is asserted low, q must be all zeros
    reset_low_forces_q_zero: assert property (
        @(posedge clk) !rst_l |-> (q == {SIZE{1'b0}})
    );

    // While reset is asserted low, so must be all zeros (since so==q)
    reset_low_forces_so_zero: assert property (
        @(posedge clk) !rst_l |-> (so == {SIZE{1'b0}})
    );

    // One cycle after reset was low, q must still be all zeros
    q_zero_one_cycle_after_reset_low: assert property (
        @(posedge clk) $past(!rst_l) |-> (q == {SIZE{1'b0}})
    );

    // One cycle after reset was low, so must still be all zeros
    so_zero_one_cycle_after_reset_low: assert property (
        @(posedge clk) $past(!rst_l) |-> (so == {SIZE{1'b0}})
    );

    // With se=1 (scan), q loads si on the next cycle
    capture_si_when_se: assert property (
        @(posedge clk) disable iff (!rst_l) se |=> (q == $past(si))
    );

    // With se=0 (functional), q loads din on the next cycle
    capture_din_when_not_se: assert property (
        @(posedge clk) disable iff (!rst_l) !se |=> (q == $past(din))
    );

    // General mux behavior: q next equals prior selected input when not in reset
    selected_mux_update: assert property (
        @(posedge clk) disable iff (!rst_l) 1 |=> (q == $past(se ? si : din))
    );

endmodule