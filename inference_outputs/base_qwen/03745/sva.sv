```systemverilog
module counter_4bit_sync_reset_sva (
    input wire CK,
    input wire RST,
    output reg [3:0] Q
);
    // Counter increments on each clock cycle when reset is low
    counter_increment: assert property (
        @(posedge CK) disable iff (!RST) Q == Q + 1
    );
    // Counter resets to 0 on each clock cycle when reset is high
    counter_reset: assert property (
        @(posedge CK) disable iff (RST) Q == 4'b0
    );
endmodule
```