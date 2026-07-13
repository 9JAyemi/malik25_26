module timer_assertions
  #(parameter TIMEOUT = 100)
   (
    input logic        clk,
    input logic        rst,
    input logic        up_req,
    input logic        up_grant,
    input logic        up_ack,
    input logic        down_req,
    input logic        down_grant,
    input logic        down_ack,
    input logic        timeout,
    input logic [31:0] counter
    );

    localparam [31:0] TIMEOUT_VALUE = TIMEOUT;

    // Upstream grant is a direct pass-through of downstream grant.
    check_up_grant_passthrough: assert property (
        @(posedge clk) disable iff (rst) up_grant == down_grant
    );

    // Downstream acknowledge is a direct pass-through of upstream acknowledge.
    check_down_ack_passthrough: assert property (
        @(posedge clk) disable iff (rst) down_ack == up_ack
    );

    // Timeout is asserted exactly when the counter reaches TIMEOUT.
    check_timeout_definition: assert property (
        @(posedge clk) disable iff (rst) timeout == (counter == TIMEOUT_VALUE)
    );

    // Downstream request is the upstream request masked by timeout.
    check_down_req_definition: assert property (
        @(posedge clk) disable iff (rst) down_req == (up_req & ~timeout)
    );

    // Counter is zero on the first cycle after reset deasserts.
    check_counter_zero_after_reset_release: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (counter == '0)
    );

    // Counter increments by one when grant is present and timeout is not active.
    check_counter_increment: assert property (
        @(posedge clk) disable iff (rst)
        (down_grant & ~timeout) |=> (counter == ($past(counter) + 32'd1))
    );

    // Counter clears when the increment condition is not met.
    check_counter_clear: assert property (
        @(posedge clk) disable iff (rst)
        ~(down_grant & ~timeout) |=> (counter == '0)
    );

endmodule