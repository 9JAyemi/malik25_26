```systemverilog
module axi_timer_sva (
    input logic CLK,
    input logic RESETn,
    input logic [4:0] bus2ip_addr_i_reg,
    input logic Q,
    output logic ce_expnd_i_5
);
    // Combinational logic, but still use @(posedge CLK) for assertions
    // ce_expnd_i_5 should be 1'b1 only when lut_input is 4'b1000
    lut_input_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (lut_input == 4'b1000) |-> (ce_expnd_i_5 == 1'b1)
    );
    // ce_expnd_i_5 should be 1'b0 for all other values of lut_input
    lut_input_else_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (lut_input != 4'b1000) |-> (ce_expnd_i_5 == 1'b0)
    );
    // At reset, ce_expnd_i_5 should be 1'b0
    reset_check: assert property (
        @(posedge CLK) !RESETn |-> (ce_expnd_i_5 == 1'b0)
    );
endmodule
```