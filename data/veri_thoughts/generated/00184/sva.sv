module state_machine_sva (
    input logic clk,
    input logic rst_,
    input logic [2:0] state_r
);

    localparam logic [2:0] IDLE    = 3'b000;
    localparam logic [2:0] SEND    = 3'b001;
    localparam logic [2:0] WAIT1   = 3'b010;
    localparam logic [2:0] UPDATE1 = 3'b011;
    localparam logic [2:0] WAIT2   = 3'b100;
    localparam logic [2:0] UPDATE2 = 3'b101;

    // Reset drives the machine to IDLE.
    check_reset_idle: assert property (
        @(posedge clk)
        !rst_ |-> (state_r == IDLE)
    );

    // IDLE advances to SEND on the next clock.
    check_idle_to_send: assert property (
        @(posedge clk) disable iff (!rst_)
        (state_r == IDLE) |=> (state_r == SEND)
    );

    // SEND advances to WAIT1 on the next clock.
    check_send_to_wait1: assert property (
        @(posedge clk) disable iff (!rst_)
        (state_r == SEND) |=> (state_r == WAIT1)
    );

    // WAIT1 advances to UPDATE1 on the next clock.
    check_wait1_to_update1: assert property (
        @(posedge clk) disable iff (!rst_)
        (state_r == WAIT1) |=> (state_r == UPDATE1)
    );

    // UPDATE1 advances to WAIT2 on the next clock.
    check_update1_to_wait2: assert property (
        @(posedge clk) disable iff (!rst_)
        (state_r == UPDATE1) |=> (state_r == WAIT2)
    );

    // WAIT2 advances to UPDATE2 on the next clock.
    check_wait2_to_update2: assert property (
        @(posedge clk) disable iff (!rst_)
        (state_r == WAIT2) |=> (state_r == UPDATE2)
    );

    // UPDATE2 wraps back to IDLE on the next clock.
    check_update2_to_idle: assert property (
        @(posedge clk) disable iff (!rst_)
        (state_r == UPDATE2) |=> (state_r == IDLE)
    );

    // Any invalid state encoding returns to IDLE on the next clock.
    check_invalid_state_to_idle: assert property (
        @(posedge clk) disable iff (!rst_)
        !((state_r == IDLE) || (state_r == SEND) || (state_r == WAIT1) ||
          (state_r == UPDATE1) || (state_r == WAIT2) || (state_r == UPDATE2))
        |=> (state_r == IDLE)
    );

    // After any non-reset cycle, the next state is always a legal encoding.
    check_next_state_is_legal: assert property (
        @(posedge clk) disable iff (!rst_)
        1'b1 |=> ((state_r == IDLE) || (state_r == SEND) || (state_r == WAIT1) ||
                  (state_r == UPDATE1) || (state_r == WAIT2) || (state_r == UPDATE2))
    );

endmodule