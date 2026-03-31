```systemverilog
module my_mac_sva (
    input logic clk,
    input logic reset,
    input logic ce,
    input logic [31:0] din0,
    input logic [31:0] din1,
    output logic [31:0] dout
);
    ///// Sequential logic /////
    // dout is reset to 0 on the rising edge of clk when reset is asserted.
    reset_dout: assert property (
        @(posedge clk) disable iff (!reset) reset |-> (dout == 32'b0)
    );
    // dout is updated on the rising edge of clk when ce is asserted.
    update_dout: assert property (
        @(posedge clk) disable iff (!reset) ce |-> (dout == dout + din0 * din1)
    );
endmodule
```