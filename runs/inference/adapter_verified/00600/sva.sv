module test_in_sva (
    input logic        clk,
    input logic        rst,
    input logic        enable,
    input logic [1:0]  ready,
    input logic [23:0] size,
    input logic [1:0]  activate,
    input logic [31:0] data,
    input logic        strobe
);

// Reset clears all state and outputs.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |-> (activate == 2'b00) && (data == 32'd0) && (strobe == 1'b0)
    );

// With ready[0]==1 and activate==0, activate[0] is set on the next cycle.
    check_activate0_on_ready0: assert property (
        @(posedge clk) disable iff (rst)
        (ready[0] && !activate && enable) |=> (activate == 2'b01)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
    check_activate1_on_ready1: assert property (
        @(posedge clk) disable iff (rst)
        (!ready[0] && !activate && enable) |=> (activate == 2'b10)
    );

// With ready[0]==0 and activate==0, activate[1] is set on the next cycle.
   