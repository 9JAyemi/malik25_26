```systemverilog
module test_in_sva (
    input logic clk,
    input logic rst,
    input logic enable,
    input logic [1:0] ready,
    input logic [23:0] size,
    output logic [1:0] activate,
    output logic [31:0] data,
    output logic strobe
);
    // Reset behavior: At reset, activate, data, and strobe should be low
    reset: assert property (
        @(posedge clk) disable iff (!rst) (rst |-> (activate == 0) && (data == 0) && (strobe == 0))
    );

    // Enable behavior: When enable is high and ready is non-zero, activate should be set
    enable_ready: assert property (
        @(posedge clk) disable iff (!rst) ((enable && (ready > 0)) |-> (activate != 0))
    );

    // Activate behavior: When activate is set, strobe should be high and data should increment
    activate_strobe: assert property (
        @(posedge clk) disable iff (!rst) (activate |-> (strobe == 1) && (data == count))
    );

    // Count behavior: When activate is set, count should increment until it reaches size
    count_increment: assert property (
        @(posedge clk) disable iff (!rst) (activate |-> (count < size) |-> (count == count + 1))
    );

    // Activate reset behavior: When activate is set and count reaches size, activate should be reset
    activate_reset: assert property (
        @(posedge clk) disable iff (!rst) (activate && (count == size) |-> (activate == 0))
    );

    // Strobe reset behavior: When strobe is high, it should be reset on the next clock edge
    strobe_reset: assert property (
        @(posedge clk) disable iff (!rst) (strobe |-> (strobe == 0))
    );

    // Data behavior: When activate is set, data should be equal to count
    data_match: assert property (
        @(posedge clk) disable iff (!rst) (activate |-> (data == count))
    );

    // Ready behavior: When activate is set and ready[0] is high, activate[0] should be set
    ready_set: assert property (
        @(posedge clk) disable iff (!rst) (activate && ready[0] |-> (activate[0] == 1))
    );

    // Ready behavior: When activate is set and ready[0] is low, activate[1] should be set
    ready_clear: assert property (
        @(posedge clk) disable iff (!rst) (activate && !ready[0] |-> (activate[1] == 1))
    );

    // Count range behavior: Count should not exceed size
    count_range: assert property (
        @(posedge clk) disable iff (!rst) (count <= size)
    );

    // Activate non-zero behavior: When activate is set, it should not be zero
    activate_nonzero: assert property (
        @(posedge clk) disable iff (!rst) (activate |-> (activate != 0))
    );
endmodule
```