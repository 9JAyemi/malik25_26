```systemverilog
module shift_reg_sva (
    input logic CLK,
    input logic RST,
    input logic LD,
    input logic [3:0] D,
    output logic [3:0] OUT
);
    // Reset behavior: At reset, all shift register outputs should be 0.
    reset: assert property (
        @(posedge CLK) disable iff (!RST) (OUT == 4'b0)
    );

    // Load behavior: When LD is high, the shift register should load the value of D.
    load: assert property (
        @(posedge CLK) disable iff (!RST) (LD |-> (OUT == D))
    );

    // Shift behavior: When LD is low, the shift register should shift the values.
    shift: assert property (
        @(posedge CLK) disable iff (!RST) (!LD |-> (OUT == reg1))
    );

    // Internal register behavior: reg4 should always be the output.
    internal_reg: assert property (
        @(posedge CLK) disable iff (!RST) (OUT == reg4)
    );

    // Internal register behavior: reg3 should shift to reg4.
    internal_reg3_to_reg4: assert property (
        @(posedge CLK) disable iff (!RST) (reg4 == reg3)
    );

    // Internal register behavior: reg2 should shift to reg3.
    internal_reg2_to_reg3: assert property (
        @(posedge CLK) disable iff (!RST) (reg3 == reg2)
    );

    // Internal register behavior: reg1 should shift to reg2.
    internal_reg1_to_reg2: assert property (
        @(posedge CLK) disable iff (!RST) (reg2 == reg1)
    );

    // Internal register behavior: reg1 should load D when LD is high.
    internal_reg1_load: assert property (
        @(posedge CLK) disable iff (!RST) (LD |-> (reg1 == D))
    );

    // Internal register behavior: reg1 should hold the previous value of reg2 when LD is low.
    internal_reg1_hold: assert property (
        @(posedge CLK) disable iff (!RST) (!LD |-> (reg1 == reg2))
    );

    // Internal register behavior: reg2 should hold the previous value of reg3 when LD is low.
    internal_reg2_hold: assert property (
        @(posedge CLK) disable iff (!RST) (!LD |-> (reg2 == reg3))
    );

    // Internal register behavior: reg3 should hold the previous value of reg4 when LD is low.
    internal_reg3_hold: assert property (
        @(posedge CLK) disable iff (!RST) (!LD |-> (reg3 == reg4))
    );
endmodule
```