```systemverilog
module binary_counter_sva (
    input logic clk,
    input logic EN,
    input logic RST,
    output logic [3:0] COUNT
);
    // Reset behavior: COUNT should be 0 when RST is active
    reset: assert property (
        @(posedge clk) disable iff (!RST) COUNT == 4'b0000
    );

    // Enable behavior: COUNT should increment when EN is high and RST is low
    enable: assert property (
        @(posedge clk) disable iff (!RST) (EN == 1'b1) |-> COUNT == COUNT + 1
    );

    // Synchronous reset behavior: COUNT should be 0 after a synchronous reset
    sync_reset: assert property (
        @(posedge clk) disable iff (!RST) RST |-> COUNT == 4'b0000
    );

    // Asynchronous reset behavior: COUNT should be 0 after an asynchronous reset
    async_reset: assert property (
        @(posedge clk) disable iff (!RST) RST |-> COUNT == 4'b0000
    );

    // COUNT should not exceed 4'b1111
    count_limit: assert property (
        @(posedge clk) disable iff (!RST) COUNT <= 4'b1111
    );

    // COUNT should not be negative
    count_non_negative: assert property (
        @(posedge clk) disable iff (!RST) COUNT >= 4'b0000
    );

    // COUNT should not wrap around
    count_wraparound: assert property (
        @(posedge clk) disable iff (!RST) (COUNT == 4'b1111) |-> COUNT + 1 == 4'b0000
    );

    // COUNT should not decrement when EN is low
    count_no_decrement: assert property (
        @(posedge clk) disable iff (!RST) (EN == 1'b0) |-> COUNT == COUNT
    );

    // COUNT should not increment when RST is high
    count_no_increment_on_reset: assert property (
        @(posedge clk) disable iff (!RST) (RST == 1'b1) |-> COUNT == COUNT
    );

    // COUNT should not be zero when EN is low and RST is low
    count_non_zero_when_en_low: assert property (
        @(posedge clk) disable iff (!RST) (EN == 1'b0) |-> COUNT != 4'b0000
    );

    // COUNT should not be zero when RST is low
    count_non_zero_when_reset_low: assert property (
        @(posedge clk) disable iff (!RST) COUNT != 4'b0000
    );
endmodule
```