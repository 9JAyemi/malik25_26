module dff_sva #(
    parameter WIDTH = 1
) (
    input logic clk,
    input logic rst,
    input logic [WIDTH-1:0] inp,
    input logic [WIDTH-1:0] outp
);
    // Active-high synchronous reset drives outp to zero on the next cycle.
    reset_forces_zero_next: assert property (
        @(posedge clk) rst |=> (outp == '0)
    );

    // When not in reset, outp captures inp with one-cycle latency.
    capture_input_next: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (outp == $past(inp))
    );

    // On the cycle after reset deasserts, outp captures inp from the deasserting edge.
    capture_on_reset_release: assert property (
        @(posedge clk) $fell(rst) |=> (outp == $past(inp))
    );

    // If reset was asserted on the previous cycle, outp must be zero now.
    prev_reset_implies_zero_now: assert property (
        @(posedge clk) $past(rst) |-> (outp == '0)
    );

    // If reset is asserted on consecutive cycles, outp remains stable (stays zero).
    reset_stability: assert property (
        @(posedge clk) rst && $past(rst) |-> $stable(outp)
    );
endmodule