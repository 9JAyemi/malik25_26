module shift_register_sva (
    input logic clk,
    input logic areset,
    input logic load,
    input logic ena,
    input logic [3:0] data,
    input logic [3:0] q
);

    clocking post_cb @(posedge clk);
        input #0 areset;
        input #0 q;
    endclocking

    // Reset drives q to 0.
    check_reset_clears_q: assert property (
        @(posedge clk) !post_cb.areset |-> (post_cb.q == 4'b0000)
    );

    // Load captures data on the clock edge.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (!post_cb.areset)
        areset && load |-> (post_cb.q == data)
    );

    // Load has priority over enable.
    check_load_priority_over_enable: assert property (
        @(posedge clk) disable iff (!post_cb.areset)
        areset && load && ena |-> (post_cb.q == data)
    );

    // Enable rotates q as {q[2:0], q[3]} when not loading.
    check_enable_rotates_q: assert property (
        @(posedge clk) disable iff (!post_cb.areset)
        areset && !load && ena |-> (post_cb.q == {q[2:0], q[3]})
    );

    // With neither load nor enable, q holds its value.
    check_idle_holds_q: assert property (
        @(posedge clk) disable iff (!post_cb.areset)
        areset && !load && !ena |-> (post_cb.q == q)
    );

endmodule