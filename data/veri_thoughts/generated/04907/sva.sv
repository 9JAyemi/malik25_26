module edge_detect_assertions (
    input logic clk,
    input logic rst_n,
    input logic a,
    input logic rise,
    input logic fall
);

    // Outputs are cleared while reset is active.
    check_reset_clears_outputs: assert property (
        @(posedge clk) (rst_n == 1'b0) |-> ((rise == 1'b0) && (fall == 1'b0))
    );

    // A sampled 0->1 transition raises rise and clears fall.
    check_rise_detect_after_active_cycle: assert property (
        @(posedge clk) disable iff (!rst_n)
        (($past(rst_n) === 1'b1) && ($past(a) === 1'b0) && (a == 1'b1)) |-> ((rise == 1'b1) && (fall == 1'b0))
    );

    // A sampled 1->0 transition raises fall and clears rise.
    check_fall_detect_after_active_cycle: assert property (
        @(posedge clk) disable iff (!rst_n)
        (($past(rst_n) === 1'b1) && ($past(a) === 1'b1) && (a == 1'b0)) |-> ((rise == 1'b0) && (fall == 1'b1))
    );

    // If a stays low, neither edge output is asserted.
    check_no_edge_when_a_stays_low: assert property (
        @(posedge clk) disable iff (!rst_n)
        (($past(rst_n) === 1'b1) && ($past(a) === 1'b0) && (a == 1'b0)) |-> ((rise == 1'b0) && (fall == 1'b0))
    );

    // If a stays high, neither edge output is asserted.
    check_no_edge_when_a_stays_high: assert property (
        @(posedge clk) disable iff (!rst_n)
        (($past(rst_n) === 1'b1) && ($past(a) === 1'b1) && (a == 1'b1)) |-> ((rise == 1'b0) && (fall == 1'b0))
    );

    // On the first clock after reset, a high input produces rise.
    check_rise_after_reset_release_with_a_high: assert property (
        @(posedge clk) disable iff (!rst_n)
        (($past(rst_n) === 1'b0) && (a == 1'b1)) |-> ((rise == 1'b1) && (fall == 1'b0))
    );

    // On the first clock after reset, a low input produces no edge outputs.
    check_no_edge_after_reset_release_with_a_low: assert property (
        @(posedge clk) disable iff (!rst_n)
        (($past(rst_n) === 1'b0) && (a == 1'b0)) |-> ((rise == 1'b0) && (fall == 1'b0))
    );

    // rise and fall are never asserted together.
    check_rise_fall_mutually_exclusive: assert property (
        @(posedge clk) disable iff (!rst_n)
        !(rise && fall)
    );

    // rise can only be high when the current input is high.
    check_rise_requires_a_high: assert property (
        @(posedge clk) disable iff (!rst_n)
        (rise == 1'b1) |-> (a == 1'b1)
    );

    // fall can only be high when the current input is low.
    check_fall_requires_a_low: assert property (
        @(posedge clk) disable iff (!rst_n)
        (fall == 1'b1) |-> (a == 1'b0)
    );

endmodule